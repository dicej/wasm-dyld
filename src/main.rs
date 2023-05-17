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

fn make_env_module(metadata: impl IntoIterator<Item = (&str, &Metadata)>) -> Vec<u8> {
    let mut memory_offset = STACK_SIZE_BYTES;
    let mut table_offset = 0;
    let mut globals = GlobalSection::new();
    let mut exports = ExportSection::new();
    let mut global_count = 0;

    let memory_size = {
        let mut add_global = |name, value, mutable| {
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

        add_global("__stack_pointer", STACK_SIZE_BYTES, true);

        for (name, metadata) in metadata {
            memory_offset = align(memory_offset, metadata.mem_info.memory_alignment);
            table_offset = align(table_offset, metadata.mem_info.table_alignment);

            add_global(&format!("{name}:memory_base"), memory_offset, false);
            add_global(&format!("{name}:table_base"), table_offset, false);

            memory_offset += metadata.mem_info.memory_size;
            table_offset += metadata.mem_info.table_size;

            for import in &metadata.memory_address_imports {
                add_global(&format!("{name}:{import}"), 0, true);
            }

            for import in &metadata.table_address_imports {
                add_global(&format!("{name}:{import}"), 0, true);
            }
        }

        memory_offset = align(memory_offset, HEAP_ALIGNMENT_BYTES);
        add_global("__heap_base", memory_offset, true);

        let heap_end = align(memory_offset, PAGE_SIZE_BYTES);
        add_global("__heap_end", heap_end, true);
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
) -> Vec<u8> {
    let mut types = TypeSection::new();
    types.function([], []);

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

    for (name, metadata) in metadata {
        imports.import(
            "env",
            &format!("{name}:{memory_base}"),
            GlobalType {
                val_type: ValType::I32,
                mutable: false,
            },
        );

        if metadata.has_data_relocs {
            imports.import(name, "__wasm_apply_data_relocs", EntityType::Function(0));
        }

        if metadata.has_ctors {
            imports.import(name, "__wasm_call_ctors", EntityType::Function(0));
        }

        for import in &metadata.memory_address_imports {
            imports.import(
                "env",
                &format!("{name}:{import}"),
                GlobalType {
                    val_type: ValType::I32,
                    mutable: true,
                },
            );

            let export = Export {
                name: import,
                ty: Type::Global {
                    ty: ValueType::I32,
                    mutable: false,
                },
            };

            if let Some(exporter) = exports.get(&export) {
                imports.import(
                    exporter,
                    import,
                    GlobalType {
                        val_type: ValType::I32,
                        mutable: true,
                    },
                );
            } else {
                bail!("unable to find {export:?} in any library");
            }

            todo!();
        }
    }
}

fn link(libraries: &[(&str, Vec<u8>)]) -> Result<Vec<u8>> {
    let mut component = Component::new();

    for (_, module) in libraries {
        component.section(&RawSection {
            id: ComponentSectionId::CoreModule.into(),
            data: module,
        });
    }

    let metadata = libraries
        .iter()
        .map(|(_, module)| Metadata::extract(module))
        .collect::<Result<Vec<_>>>()?;

    let env = make_env_module(libraries.iter().map(|(name, _)| *name).zip(&metadata));
    component.section(&RawSection {
        id: ComponentSectionId::CoreModule.into(),
        data: &env,
    });

    let mut exports = HashMap::new();
    for (name, metadata) in libraries.iter().map(|(name, _)| *name).zip(&metadata) {
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

    let init = make_init_module(
        libraries.iter().map(|(name, _)| *name).zip(&metadata),
        &exports,
    );

    Ok(component.finish())
}
