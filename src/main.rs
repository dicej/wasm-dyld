#![deny(warnings)]

use {
    anyhow::{anyhow, Result},
    std::fs,
    wasm_encoder::{Component, RawSection},
};

const PAGE_SIZE_BYTES: u32 = 65536;
const STACK_SIZE_BYTES: u32 = PAGE_SIZE_BYTES;
const HEAP_ALIGNMENT_BYTES: u32 = 16;

/// WebAssembly ahead-of-time dynamic linker
///
/// This tool takes one or more shared library Wasm files and produces a component which links them together.
#[derive(clap::Parser, Debug)]
#[command(author, version, about)]
struct Options {
    /// One or more libraries to link together
    ///
    /// Each of these files must conform to
    /// https://github.com/WebAssembly/tool-conventions/blob/main/DynamicLinking.md.
    libraries: Vec<PathBuf>,

    /// Output file to which to write the resulting component
    ///
    /// See https://github.com/WebAssembly/component-model for details on the format of this file.
    #[arg(short = 'o', long, default_value = "linked.wasm")]
    output: PathBuf,
}

fn main() -> Result<()> {
    let options = Options::parse();

    fs::write(
        &options.output,
        link(
            &options
                .libraries
                .iter()
                .map(|path| {
                    Ok((
                        path.file_name().and_then(OsStr::to_str).ok_or_else(|| {
                            anyhow!("unable to get file name as UTF-8 from {}", path.display())
                        }),
                        fs::read(path)?,
                    ))
                })
                .collect::<Result<Vec<_>>>()?,
        )?,
    )?;

    Ok(())
}

fn get_and_increment(n: &mut usize) -> usize {
    let v = *n;
    *n += 1;
    v
}

fn make_env_module(metadata: impl IntoIterator<Item = (&str, &Metadata)>) -> Vec<u8> {
    let mut memory_offset = STACK_SIZE_BYTES;
    let mut table_offset = 0;
    let mut globals = GlobalSection::new();
    let mut exports = ExportSection::new();
    let mut global_count = 0;

    let memory_size = {
        let mut add_global_export = |name, value, mutable| {
            globals.global(
                GlobalType {
                    val_type: ValType::I32,
                    mutable,
                },
                ConstExpr::i32_const(value),
            );
            exports.export(name, kind: ExportKind::Global, global_count);
            global_count += 1;
        };

        add_global_export("__stack_pointer", STACK_SIZE_BYTES, true);

        for (name, metadata) in metadata {
            memory_offset = align(memory_offset, metadata.mem_info.memory_alignment);
            table_offset = align(table_offset, metadata.mem_info.table_alignment);

            add_global_export(&format!("{name}:memory_base"), memory_offset, false);
            add_global_export(&format!("{name}:table_base"), table_offset, false);

            memory_offset += metadata.mem_info.memory_size;
            table_offset += metadata.mem_info.table_size;

            for import in metadata
                .memory_address_imports
                .iter()
                .chain(&metadata.table_address_imports)
            {
                add_global_export(&format!("{name}:{import}"), 0, true);
            }
        }

        memory_offset = align(memory_offset, HEAP_ALIGNMENT_BYTES);
        add_global_export("__heap_base", memory_offset, true);

        let heap_end = align(memory_offset, PAGE_SIZE_BYTES);
        add_global_export("__heap_end", heap_end, true);
        heap_end / PAGE_SIZE_BYTES
    };

    let mut module = Module::new();

    {
        let mut memories = MemorySection::new();
        memories.memory(MemoryType {
            minimum: memory_size,
            maximum: None,
            memory64: false,
            shared: false,
        });
        exports.export("memory", kind: ExportKind::Memory, 0);
        module.section(&memories);
    }

    {
        let mut tables = TableSection::new();
        tables.table(TableType {
            element_type: RefType {
                nullable: true,
                heap_type: HeapType::Func,
            },
            minimum: table_offset,
            maximum: None,
        });
        exports.export("__indirect_function_table", kind: ExportKind::Table, 0);
        module.section(&tables);
    }

    module.section(&globals);
    module.section(&exports);

    module.finish()
}

fn make_init_module(
    metadata: impl IntoIterator<Item = (&str, &Metadata)>,
    exports: &HashMap<&Export, &str>,
) -> Result<Vec<u8>> {
    let mut module = Module::new();

    let mut types = TypeSection::new();
    types.function([], []);
    module.section(&types);

    let mut imports = ImportSection::new();
    imports.import(
        "env",
        "__indirect_function_table",
        TableType {
            element_type: RefType {
                nullable: true,
                heap_type: HeapType::Func,
            },
            minimum: 0,
            maximum: None,
        },
    );

    let mut global_count = 0;
    let add_global_import = |imports, module, name, mutable| {
        imports.import(
            module,
            name,
            GlobalType {
                val_type: ValType::I32,
                mutable,
            },
        );
        get_and_increment(&mut global_count)
    };

    let mut function_count = 0;
    let add_function_import = |imports, module, name| {
        imports.import(module, name, EntityType::Function(0));
        get_and_increment(&mut global_count)
    };

    let mut memory_address_inits = Vec::new();
    let mut table_address_inits = Vec::new();
    let mut reloc_calls = Vec::new();
    let mut ctor_calls = Vec::new();

    for (name, metadata) in metadata {
        let memory_base =
            add_global_import(&mut imports, "env", &format!("{name}:memory_base"), false);

        let table_base =
            add_global_import(&mut imports, "env", &format!("{name}:table_base"), false);

        if metadata.has_data_relocs {
            reloc_calls.push(Ins::Call(add_function_import(
                &mut imports,
                name,
                "__wasm_apply_data_relocs",
            )));
        }

        if metadata.has_ctors {
            ctor_calls.push(Ins::Call(add_function_import(
                &mut imports,
                name,
                "__wasm_call_ctors",
            )));
        }

        let make_init = |import, inits, base| {
            inits.push(Ins::GlobalGet(base));
            inits.push(Ins::GlobalGet(add_global_import(
                &mut imports,
                find_offset_exporter(import)?,
                import,
                false,
            )));
            inits.push(Ins::I32Add);
            inits.push(Ins::GlobalSet(add_global_import(
                &mut imports,
                "env",
                &format!("{name}:{import}"),
                true,
            )));
        };

        for import in &metadata.memory_address_imports {
            make_init(import, &mut memory_address_inits, memory_base);
        }

        for import in &metadata.table_address_imports {
            make_init(import, &mut table_address_inits, table_base);
        }
    }

    module.section(&imports);

    let mut functions = FunctionSection::new();
    functions.function(0);
    module.section(&functions);

    let mut code_section = CodeSection::new();
    let mut function = Function::new([]);
    for ins in memory_address_inits
        .chain(&table_address_inits)
        .chain(&reloc_calls)
        .chain(&ctor_calls)
    {
        function.instruction(ins);
    }
    function.instruction(&Ins::End);
    code_section.function(&function);
    module.section(&code_section);

    Ok(module.finish())
}

fn find_offset_exporter<'a>(name: &str, exports: &HashMap<&Export, &'a str>) -> Result<&'a str> {
    let export = Export {
        name,
        ty: Type::Global {
            ty: ValueType::I32,
            mutable: false,
        },
    };

    exports
        .get(&export)
        .ok_or_else(|| anyhow!("unable to find {export:?} in any library"))
}

fn find_function_exporter<'a>(
    name: &str,
    ty: &FunctionType,
    exports: &HashMap<&Export, &'a str>,
) -> Result<&'a str> {
    let export = Export {
        name,
        ty: Type::Function(ty.clone()),
    };

    exports
        .get(&export)
        .ok_or_else(|| anyhow!("unable to find {export:?} in any library"))
}

fn resolve_exports<'a>(
    metadata: impl IntoIterator<Item = (&'a str, &'a Metadata)>,
) -> Result<HashMap<&'a Export, &'a str>> {
    let mut exports = HashMap::new();
    for (name, metadata) in metadata {
        for export in &metadata.exports {
            let entry = exports.entry(export);
            match entry {
                Entry::Occupied(entry) => {
                    bail!("duplicate export in {name} and {}: {export:?}", entry.get())
                }
                Entry::Vacant(entry) => entry.insert(name),
            }
        }
    }
}

fn make_wasi_stub(name: &str) -> Vec<Ins> {
    // For most stubs, we trap, but we need specialized stubs for the functions called by `wasi-libc`'s
    // __wasm_call_ctors; otherwise we'd trap immediately upon calling any export.
    match name {
        "clock_time_get" => vec![
            // *time = 0;
            Ins::LocalGet(2),
            Ins::I64Const(0),
            Ins::I64Store(bindgen::mem_arg(0, 3)),
            // return ERRNO_SUCCESS;
            Ins::I32Const(0),
        ],
        "environ_sizes_get" => vec![
            // *environc = 0;
            Ins::LocalGet(0),
            Ins::I32Const(0),
            Ins::I32Store(bindgen::mem_arg(0, 2)),
            // *environ_buf_size = 0;
            Ins::LocalGet(1),
            Ins::I32Const(0),
            Ins::I32Store(bindgen::mem_arg(0, 2)),
            // return ERRNO_SUCCESS;
            Ins::I32Const(0),
        ],
        "fd_prestat_get" => vec![
            // return ERRNO_BADF;
            Ins::I32Const(8),
        ],
        _ => vec![Ins::Unreachable],
    }
}

fn make_wasi_module(metadata: &[Metadata]) -> Vec<u8> {
    let mut module = Module::new();
    let mut types = TypeSection::new();
    let mut functions = FunctionSection::new();
    let mut code_section = CodeSection::new();
    let mut count = 0;

    for metadata in metadata {
        for (name, ty) in &metadata.wasi_imports {
            types.function(
                ty.parameters.iter().copied().map(ValType::into),
                ty.results.iter().copied().map(ValType::into),
            );
            functions.function(count);
            let mut function = Function::new([]);
            for ins in &make_wasi_stub(*name) {
                function.instruction(ins);
            }
            code_section.function(&function);
            count += 1;
        }
    }

    module.section(&types);
    module.section(&functions);
    module.section(&code_section);

    module.finish()
}

fn topo_sort(
    metadata: impl IntoIterator<Item = (&str, &Metadata)>,
    exports: &HashMap<&Export, &str>,
) -> Result<Vec<usize>> {
    let mut needs = HashMap::new();
    let mut names = Vec::new();
    for (index, (name, metadata)) in metadata.into_iter().enumerate() {
        names.insert((name, index));
        for (name, ty) in &metadata.env_imports {
            needs
                .entry(name)
                .or_default()
                .insert(find_function_exporter(name, ty, exports)?);
        }
    }

    let empty = &HashMap::new();

    loop {
        let mut new = HashMap::new();
        for (name, exporters) in &needs {
            for exporter in exporters {
                for exporter in needs.get(exporter).unwrap_or(empty) {
                    if !exporters.contains(exporter) {
                        new.entry(name).or_default().insert(exporter);
                    }
                }
            }
        }

        if new.is_empty() {
            break;
        } else {
            for (name, exporters) in new {
                needs.entry(name).or_default().extend(exporters);
            }
        }
    }

    for (name, exporters) in &needs {
        if exporters.contains(name) {
            bail!("todo: cyclic function dependencies not yet supported");
        }
    }

    indexes.sort_by(|a, b| {
        if needs.get(a.0).unwrap_or(empty).contains(b.0) {
            Ordering::Greater
        } else if needs.get(b.0).unwrap_or(empty).contains(a.0) {
            Ordering::Less
        } else {
            unreachable!()
        }
    });

    Ok(indexes.into_iter().map(|(_, index)| index).collect())
}

fn link(libraries: &[(&str, Vec<u8>)]) -> Result<Vec<u8>> {
    let metadata = libraries
        .iter()
        .map(|(_, module)| Metadata::extract(module))
        .collect::<Result<Vec<_>>>()?;

    let exports = resolve_exports(libraries.iter().map(|(name, _)| *name).zip(&metadata))?;

    let topo_sorted = topo_sort(
        libraries.iter().map(|(name, _)| *name).zip(&metadata),
        &exports,
    )?;

    let mut component = Component::new();
    let mut instances = InstanceSection::new();
    let mut aliases = ComponentAliasSection::new();

    {
        let mut module_count = 0;
        let add_module = |data| {
            component.section(&RawSection {
                id: ComponentSectionId::CoreModule.into(),
                data,
            });
            get_and_increment(&mut module_count)
        };

        let mut alias_count = 0;
        let add_alias = |name, kind, instance| {
            aliases.alias(Alias::CoreInstanceExport {
                instance,
                kind,
                name,
            });
            get_and_increment(&mut alias_count)
        };

        let mut instance_count = 0;
        let export_items = |count, items| {
            instances.export_items(items);
            get_and_increment(count)
        };

        let instantiate = |count, module, args| {
            instances.instantiate(module, args);
            get_and_increment(count)
        };

        let wasi = instantiate(
            &mut instance_count,
            add_module(&make_wasi_module(&metadata)),
            [],
        );

        let env = instantiate(
            &mut instance_count,
            add_module(&make_env_module(
                libraries.iter().map(|(name, _)| *name).zip(&metadata),
            )),
            [],
        );

        let default_items = [
            ("memory", ExportKind::Memory, env, "memory"),
            (
                "__indirect_function_table",
                ExportKind::Table,
                env,
                "__indirect_function_table",
            ),
            (
                "__stack_pointer",
                ExportKind::Global,
                env,
                "__stack_pointer",
            ),
        ]
        .into_iter()
        .map(|(name, kind, instance, instance_name)| {
            (name, kind, add_alias(instance_name, kind, instance))
        })
        .collect::<Vec<_>>();

        let mut instance_map = HashMap::new();
        for index in topo_sorted {
            let (name, module) = &libraries[index];
            let my_env = export_items(
                &mut instance_count,
                default_items.into_iter().chain(
                    [
                        (
                            "__memory_base",
                            ExportKind::Global,
                            env,
                            &format!("{name}:memory_base"),
                        ),
                        (
                            "__table_base",
                            ExportKind::Global,
                            env,
                            &format!("{name}:table_base"),
                        ),
                    ]
                    .into_iter()
                    .chain(metadata[index].env_imports.iter().map(|(name, ty)| {
                        (
                            name,
                            ExportKind::Func,
                            instance_map
                                .get(find_function_exporter(name, ty, exports).unwrap())
                                .unwrap(),
                            name,
                        )
                    }))
                    .map(|(name, kind, instance, instance_name)| {
                        (name, kind, add_alias(instance_name, kind, instance))
                    }),
                ),
            );

            instance_map.insert(
                name,
                instantiate(
                    &mut instance_count,
                    add_module(module),
                    [
                        ("GOT.mem", ModuleArg::Instance(env)),
                        ("GOT.func", ModuleArg::Instance(env)),
                        ("wasi_snapshot_preview1", ModuleArg::Instance(wasi)),
                        ("env", my_env),
                    ],
                ),
            );
        }

        let init = instantiate(
            &mut instance_count,
            add_module(&make_init_module(
                libraries.iter().map(|(name, _)| *name).zip(&metadata),
                &exports,
            )?),
            iter::once(("env", ModuleArg::Instance(env))).chain(
                libraries
                    .iter()
                    .map(|(name, _)| (name, instance_map.get(name).unwrap())),
            ),
        );
    }

    component.section(&aliases);
    component.section(&instances);

    Ok(component.finish())
}
