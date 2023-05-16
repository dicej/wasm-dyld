#![deny(warnings)]

use {
    anyhow::{anyhow, Result},
    std::fs,
    wasm_encoder::{Component, RawSection},
};

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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum ImportType {
    Function,
    Global,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Import<'a> {
    module: &'a str,
    name: &'a str,
    ty: ImportType,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum ExportType {
    Function,
    Global,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Export<'a> {
    name: &'a str,
    ty: ExportType,
}

#[derive(Debug, Default)]
struct Metadata<'a> {
    needs_memory: bool,
    needs_table: bool,
    needs_stack_pointer: bool,
    needs_heap_base: bool,
    needs_heap_end: bool,
    has_start: bool,
    imports: HashSet<Import<'a>>,
    exports: HashSet<Export<'a>>,
}

impl<'a> Metadata<'a> {
    fn extract(module: &'a [u8]) -> Result<Self> {
        let mut result = Self::default();
        let mut types = Vec::new();

        for payload in Parser::new(0).parse_all(module) {
            match payload? {
                Payload::TypeSection(reader) => {
                    types = reader.into_iter().collect::<Result<Vec<_>, _>>()?;
                }

                Payload::ImportSection(reader) => {
                    let mut imports = ImportSection::new();
                    for import in reader {
                        let type_error = || {
                            bail!(
                                "unexpected type for {}:{}: {:?}",
                                import.module,
                                import.name,
                                import.ty
                            )
                        };

                        match (import.module, import.name) {
                            ("env", "memory") => {
                                if let wasmparser::TypeRef::Memory(_) = import.ty {
                                    result.needs_memory = true;
                                } else {
                                    return type_error();
                                }
                            }
                            ("env", "__memory_base") => {
                                if let wasmparser::TypeRef::Global(wasmparser::GlobalType {
                                    content_type: wasmparser::ValType::I32,
                                    ..
                                }) = import.ty
                                {
                                    result.needs_memory = true;
                                } else {
                                    return type_error();
                                }
                            }
                            ("env", "__indirect_function_table") => {
                                if let wasmparser::TypeRef::Table(wasmparser::TableType {
                                    element_type,
                                    initial: 0,
                                    maximum: None,
                                }) = import.ty
                                {
                                    if element_type == RefType::FUNCREF {
                                        result.needs_table = true;
                                    } else {
                                        return type_error();
                                    }
                                } else {
                                    return type_error();
                                }
                            }
                            ("env", "__table_base") => {
                                if let wasmparser::TypeRef::Global(wasmparser::GlobalType {
                                    content_type: wasmparser::ValType::I32,
                                    ..
                                }) = import.ty
                                {
                                    result.needs_table = true;
                                } else {
                                    return type_error();
                                }
                            }
                            ("env", "__stack_pointer") => {
                                if let wasmparser::TypeRef::Global(wasmparser::GlobalType {
                                    content_type: wasmparser::ValType::I32,
                                    ..
                                }) = import.ty
                                {
                                    result.needs_stack_pointer = true;
                                } else {
                                    return type_error();
                                }
                            }
                            ("GOT.mem", "__heap_base") => {
                                if let wasmparser::TypeRef::Global(wasmparser::GlobalType {
                                    content_type: wasmparser::ValType::I32,
                                    ..
                                }) = import.ty
                                {
                                    result.needs_heap_base = true;
                                } else {
                                    return type_error();
                                }
                            }
                            ("GOT.mem", "__heap_end") => {
                                if let wasmparser::TypeRef::Global(wasmparser::GlobalType {
                                    content_type: wasmparser::ValType::I32,
                                    ..
                                }) = import.ty
                                {
                                    result.needs_heap_end = true;
                                } else {
                                    return type_error();
                                }
                            }
                            (module, name) => result.imports.insert(Import {
                                module,
                                name,
                                ty: match import.ty {
                                    wasmparser::TypeRef::Func(ty) => {
                                        Type::Function(FunctionType::from(types[*ty]))
                                    }
                                    wasmparser::TypeRef::Global(wasmparser::GlobalType {
                                        content_type,
                                        mutable,
                                    }) => Type::Global {
                                        ty: ValueType::try_from(content_type)?,
                                        mutable,
                                    },
                                    ty => {
                                        bail!("unsupported import ty for {}: {ty:?}", export.name)
                                    }
                                },
                            }),
                        }
                    }
                }

                Payload::ExportSection(reader) => {
                    let mut exports = ExportSection::new();
                    for export in reader {
                        result.exports.insert(Export {
                            name: export.name,
                            ty: match export.kind {
                                wasmparser::ExternalKind::Func => {
                                    Type::Function(FunctionType::from(function_types[export.index]))
                                }
                                wasmparser::ExternalKind::Global => {
                                    let ty = global_types[export.index];
                                    Type::Global {
                                        ty: ValueType::try_from(ty.content_type),
                                        mutable: ty.mutable,
                                    }
                                }
                                kind => {
                                    bail!("unsupported export kind for {}: {kind:?}", export.name)
                                }
                            },
                        });
                    }
                }

                Payload::StartSection { func, .. } => result.has_start = true,

                _ => {}
            }
        }

        Ok(result)
    }
}

fn link(libraries: &[(&str, Vec<u8>)]) -> Result<Vec<u8>> {
    let metadata = libraries
        .iter()
        .map(|(_, module)| Metadata::extract(module))
        .collect::<Result<Vec<_>>>()?;

    let mut component = Component::new();

    for (_, module) in libraries {
        component.section(&RawSection {
            id: ComponentSectionId::CoreModule.into(),
            data: module,
        });
    }

    Ok(component.finish())
}
