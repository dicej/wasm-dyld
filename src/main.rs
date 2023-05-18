#![deny(warnings)]

use {
    anyhow::{anyhow, bail, Error, Result},
    clap::Parser as _,
    metadata::{Export, FunctionType, GlobalType, Metadata, Type, ValueType},
    std::{
        cmp::Ordering,
        collections::{hash_map::Entry, HashMap, HashSet},
        ffi::OsStr,
        fs, iter,
        path::PathBuf,
    },
    wasm_encoder::{
        Alias, CodeSection, Component, ComponentAliasSection, ComponentSectionId, ConstExpr,
        EntityType, ExportKind, ExportSection, Function, FunctionSection, GlobalSection, HeapType,
        ImportSection, InstanceSection, Instruction as Ins, MemArg, MemorySection, MemoryType,
        Module, ModuleArg, RawSection, RefType, StartSection, TableSection, TableType, TypeSection,
        ValType,
    },
};

mod metadata;

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
                        })?,
                        fs::read(path)?,
                    ))
                })
                .collect::<Result<Vec<_>>>()?,
        )?,
    )?;

    Ok(())
}

fn align(a: u32, b: u32) -> u32 {
    assert!(b.is_power_of_two());
    (a + (b - 1)) & !(b - 1)
}

fn get_and_increment(n: &mut u32) -> u32 {
    let v = *n;
    *n += 1;
    v
}

fn make_env_module<'a>(metadata: impl IntoIterator<Item = (&'a str, &'a Metadata<'a>)>) -> Vec<u8> {
    let mut memory_offset = STACK_SIZE_BYTES;
    let mut table_offset = 0;
    let mut globals = GlobalSection::new();
    let mut exports = ExportSection::new();

    let memory_size = {
        let mut global_count = 0;
        let mut add_global_export = |name: &str, value, mutable| {
            globals.global(
                wasm_encoder::GlobalType {
                    val_type: ValType::I32,
                    mutable,
                },
                &ConstExpr::i32_const(i32::try_from(value).unwrap()),
            );
            exports.export(
                name,
                ExportKind::Global,
                get_and_increment(&mut global_count),
            );
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
            minimum: u64::from(memory_size),
            maximum: None,
            memory64: false,
            shared: false,
        });
        exports.export("memory", ExportKind::Memory, 0);
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
        exports.export("__indirect_function_table", ExportKind::Table, 0);
        module.section(&tables);
    }

    module.section(&globals);
    module.section(&exports);

    module.finish()
}

fn make_init_module<'a>(
    metadata: impl IntoIterator<Item = (&'a str, &'a Metadata<'a>)>,
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
    let mut add_global_import = |imports: &mut ImportSection, module: &str, name: &str, mutable| {
        imports.import(
            module,
            name,
            wasm_encoder::GlobalType {
                val_type: ValType::I32,
                mutable,
            },
        );
        get_and_increment(&mut global_count)
    };

    let mut function_count = 0;
    let mut add_function_import = |imports: &mut ImportSection, module, name| {
        imports.import(module, name, EntityType::Function(0));
        get_and_increment(&mut function_count)
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

        let mut make_init = |import, inits: &mut Vec<Ins>, base| {
            inits.push(Ins::GlobalGet(base));
            inits.push(Ins::GlobalGet(add_global_import(
                &mut imports,
                find_offset_exporter(import, exports)?,
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

            Ok::<_, Error>(())
        };

        for import in &metadata.memory_address_imports {
            make_init(import, &mut memory_address_inits, memory_base)?;
        }

        for import in &metadata.table_address_imports {
            make_init(import, &mut table_address_inits, table_base)?;
        }
    }

    module.section(&imports);

    let mut functions = FunctionSection::new();
    functions.function(0);
    module.section(&functions);

    let mut code_section = CodeSection::new();
    let mut function = Function::new([]);
    for ins in memory_address_inits
        .iter()
        .chain(&table_address_inits)
        .chain(&reloc_calls)
        .chain(&ctor_calls)
    {
        function.instruction(ins);
    }
    function.instruction(&Ins::End);
    code_section.function(&function);
    module.section(&code_section);

    module.section(&StartSection { function_index: 0 });

    Ok(module.finish())
}

fn find_offset_exporter<'a>(name: &str, exports: &HashMap<&Export, &'a str>) -> Result<&'a str> {
    let export = Export {
        name,
        ty: Type::Global(GlobalType {
            ty: ValueType::I32,
            mutable: false,
        }),
    };

    exports
        .get(&export)
        .copied()
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
        .copied()
        .ok_or_else(|| anyhow!("unable to find {export:?} in any library"))
}

fn resolve_exports<'a>(
    metadata: impl IntoIterator<Item = (&'a str, &'a Metadata<'a>)>,
) -> Result<HashMap<&'a Export<'a>, &'a str>> {
    let mut exports = HashMap::new();
    for (name, metadata) in metadata {
        for export in &metadata.exports {
            let entry = exports.entry(export);
            match entry {
                Entry::Occupied(entry) => {
                    bail!("duplicate export in {name} and {}: {export:?}", entry.get())
                }
                Entry::Vacant(entry) => {
                    entry.insert(name);
                }
            }
        }
    }
    Ok(exports)
}

fn mem_arg(offset: u64, align: u32) -> MemArg {
    MemArg {
        offset,
        align,
        memory_index: 0,
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
            Ins::I64Store(mem_arg(0, 3)),
            // return ERRNO_SUCCESS;
            Ins::I32Const(0),
        ],
        "environ_sizes_get" => vec![
            // *environc = 0;
            Ins::LocalGet(0),
            Ins::I32Const(0),
            Ins::I32Store(mem_arg(0, 2)),
            // *environ_buf_size = 0;
            Ins::LocalGet(1),
            Ins::I32Const(0),
            Ins::I32Store(mem_arg(0, 2)),
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
                ty.parameters.iter().copied().map(ValType::from),
                ty.results.iter().copied().map(ValType::from),
            );
            functions.function(count);
            let mut function = Function::new([]);
            for ins in &make_wasi_stub(name) {
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

fn topo_sort<'a>(
    metadata: impl IntoIterator<Item = (&'a str, &'a Metadata<'a>)>,
    exports: &HashMap<&Export, &str>,
) -> Result<Vec<usize>> {
    let mut needs = HashMap::<&str, HashSet<&str>>::new();
    let mut names = Vec::new();
    for (index, (name, metadata)) in metadata.into_iter().enumerate() {
        names.push((name, index));
        for (name, ty) in &metadata.env_imports {
            needs
                .entry(name)
                .or_default()
                .insert(find_function_exporter(name, ty, exports)?);
        }
    }

    let empty = &HashSet::new();

    loop {
        let mut new = HashMap::<&str, HashSet<&str>>::new();
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

    names.sort_by(|a, b| {
        if needs.get(a.0).unwrap_or(empty).contains(b.0) {
            Ordering::Greater
        } else if needs.get(b.0).unwrap_or(empty).contains(a.0) {
            Ordering::Less
        } else {
            unreachable!()
        }
    });

    Ok(names.into_iter().map(|(_, index)| index).collect())
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
        let mut add_module = |data: &[u8]| {
            component.section(&RawSection {
                id: ComponentSectionId::CoreModule.into(),
                data,
            });
            get_and_increment(&mut module_count)
        };

        let mut alias_count = 0;
        let mut add_alias = |name: &str, kind, instance| {
            aliases.alias(Alias::CoreInstanceExport {
                instance,
                kind,
                name,
            });
            get_and_increment(&mut alias_count)
        };

        let mut instance_count = 0;
        let export_items = |count: &mut u32, instances: &mut InstanceSection, items| {
            instances.export_items(items);
            get_and_increment(count)
        };

        let instantiate = |count: &mut u32, instances: &mut InstanceSection, module, args| {
            instances.instantiate(module, args);
            get_and_increment(count)
        };

        let wasi = instantiate(
            &mut instance_count,
            &mut instances,
            add_module(&make_wasi_module(&metadata)),
            Vec::new(),
        );

        let env = instantiate(
            &mut instance_count,
            &mut instances,
            add_module(&make_env_module(
                libraries.iter().map(|(name, _)| *name).zip(&metadata),
            )),
            Vec::new(),
        );

        let default_items = [
            ("memory", ExportKind::Memory, env),
            ("__indirect_function_table", ExportKind::Table, env),
            ("__stack_pointer", ExportKind::Global, env),
        ]
        .into_iter()
        .map(|(name, kind, instance)| (name, kind, add_alias(name, kind, instance)))
        .collect::<Vec<_>>();

        let mut instance_map = HashMap::new();
        for index in topo_sorted {
            let (name, module) = &libraries[index];

            let memory_base = format!("{name}:memory_base");
            let table_base = format!("{name}:table_base");

            let my_env = export_items(
                &mut instance_count,
                &mut instances,
                default_items
                    .iter()
                    .copied()
                    .chain(
                        [
                            (
                                "__memory_base",
                                ExportKind::Global,
                                env,
                                memory_base.as_str(),
                            ),
                            ("__table_base", ExportKind::Global, env, table_base.as_str()),
                        ]
                        .into_iter()
                        .chain(metadata[index].env_imports.iter().map(|(name, ty)| {
                            (
                                *name,
                                ExportKind::Func,
                                *instance_map
                                    .get(&find_function_exporter(name, ty, &exports).unwrap())
                                    .unwrap(),
                                *name,
                            )
                        }))
                        .map(|(name, kind, instance, instance_name)| {
                            (name, kind, add_alias(instance_name, kind, instance))
                        }),
                    )
                    .collect::<Vec<_>>(),
            );

            instance_map.insert(
                name,
                instantiate(
                    &mut instance_count,
                    &mut instances,
                    add_module(module),
                    vec![
                        ("GOT.mem", ModuleArg::Instance(env)),
                        ("GOT.func", ModuleArg::Instance(env)),
                        ("wasi_snapshot_preview1", ModuleArg::Instance(wasi)),
                        ("env", ModuleArg::Instance(my_env)),
                    ],
                ),
            );
        }

        instantiate(
            &mut instance_count,
            &mut instances,
            add_module(&make_init_module(
                libraries.iter().map(|(name, _)| *name).zip(&metadata),
                &exports,
            )?),
            iter::once(("env", ModuleArg::Instance(env)))
                .chain(libraries.iter().map(|(name, _)| {
                    (*name, ModuleArg::Instance(*instance_map.get(name).unwrap()))
                }))
                .collect(),
        );
    }

    component.section(&aliases);
    component.section(&instances);

    // todo: wire up component type(s) found in modules, if any

    Ok(component.finish())
}

#[cfg(test)]
mod tests {
    const FOO: &str = r#"
(module
  (type (func))
  (type (func (param i32) (result i32)))
  (import "env" "memory" (memory 1))
  (import "env" "__indirect_function_table" (table 0 funcref))
  (import "env" "__stack_pointer" (global $__stack_pointer (mut i32)))
  (import "env" "__memory_base" (global $__memory_base i32))
  (import "env" "__table_base" (global $__table_base i32))
  (import "env" "malloc" (func $malloc (type 0)))
  (import "env" "abort" (func $abort (type 1)))
  (import "GOT.mem" "um" (global $um (mut i32)))
  (func $__wasm_call_ctors (type 0))
  (func $__wasm_apply_data_relocs (type 0))
  (func $foo (type 1) (param i32) (result i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    global.set $__stack_pointer

    i32.const 4
    call $malloc

    block ;; label = @1
      br_if 0 (;@1;)
      call $abort
      unreachable
    end

    local.get 0
    global.get $um
    i32.load offset=16
    i32.add
    i32.const 42
    i32.add

    global.get $__stack_pointer
    i32.const 16
    i32.add
    global.set $__stack_pointer
  )
  (global i32 i32.const 0)
  (export "__wasm_call_ctors" (func $__wasm_call_ctors))
  (export "__wasm_apply_data_relocs" (func $__wasm_apply_data_relocs))
  (export "foo" (func $foo))
  (export "well" (global 3))
  (data $.data (global.get $__memory_base) "\05\00\00\00")
)
"#;

    const BAR: &str = r#"
(module
  (type (func (param i32) (result i32)))
  (type (func))
  (import "env" "memory" (memory 1))
  (import "env" "__indirect_function_table" (table 0 funcref))
  (import "env" "__memory_base" (global $__memory_base i32))
  (import "env" "__table_base" (global $__table_base i32))
  (import "env" "foo" (func $foo (type 0)))
  (import "GOT.mem" "well" (global $well (mut i32)))
  (func $__wasm_call_ctors (type 1))
  (func $__wasm_apply_data_relocs (type 1))
  (func $bar (type 0) (param i32) (result i32)
    (local i32)
    global.get $well
    local.set 1
    local.get 0
    call $foo
    local.get 1
    i32.load
    i32.add
  )
  (global i32 i32.const 0)
  (export "__wasm_call_ctors" (func $__wasm_call_ctors))
  (export "__wasm_apply_data_relocs" (func $__wasm_apply_data_relocs))
  (export "bar" (func $bar))
  (export "um" (global 3))
  (data $.data (global.get $__memory_base) "\01\00\00\00\02\00\00\00\03\00\00\00\04\00\00\00\05\00\00\00")
)
"#;

    const LIBC: &str = r#"
(module
  (type (func))
  (type (func (param i32) (result i32)))
  (import "GOT.mem" "__heap_base" (global $__heap_base (mut i32)))
  (import "GOT.mem" "__heap_end" (global $__heap_end (mut i32)))
  (global $heap (mut i32) i32.const 0)
  (func $start (type 0)
    global.get $__heap_base
    global.set $heap
  )
  (func $malloc (type 1) (param i32) (result i32)
    global.get $heap
    global.get $heap
    local.get 0
    i32.add
    global.set $heap
  )
  (func $abort (type 0)
    unreachable
  )
  (export "malloc" (func $malloc))
  (export "abort" (func $abort))
  (start $start)
"#;

    #[test]
    fn it_works() -> Result<()> {
        let (component, instance_map, aliases) = link(
            [("libfoo.so", FOO), ("libbar.so", BAR), ("libc.so", LIBC)]
                .into_iter()
                .map(|(name, wat)| Ok((name, wat::parse_str(wat)?)))
                .collect::<Result<Vec<_>>>()?,
        )?;

        todo!("no need to keep track of counts for most things; use `len` instead");

        let bar = aliases.len();
        aliases.alias(Alias::CoreInstanceExport {
            instance: *instance_map.get("libbar.so").unwrap(),
            kind: ExportKind::Func,
            name: "bar",
        });

        let mut types = ComponentTypeSection::new();
        types
            .function()
            .params(["v", PrimitiveValType::S32])
            .result(PrimitiveValType::S32);
        component.section(&types);

        let mut functions = CanonicalFunctionSection::new();
        functions.lift(bar, 0, []);
        component.section(&instances);

        let mut exports = ComponentExportSection::new();
        exports.export("init", "", ComponentExportKind::Func, 0, None);
        component.section(&exports);

        let component = component.finish();

        wasmparser::validate(&component)?;

        let mut config = Config::new();
        config.wasm_component_model(true);

        let engine = Engine::new(&config).unwrap();
        let mut linker = Linker::new(&engine);
        let mut store = Store::new(&engine, ());
        let instance = linker.instantiate(&mut store, &Component::new(&engine, &component)?)?;
        let func = instance
            .exports(&mut store)
            .ok_or_else(|| anyhow!("no inbound-http instance found"))?
            .typed_func::<(i32,), (i32,)>("bar")?;

        assert_eq!(42, func.call(&mut store, (7,))?);
    }
}
