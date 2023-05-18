#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
enum ValueType {
    I32,
    I64,
    F32,
    F64,
}

impl TryFrom<ValType> for ValueType {
    type Error = Error;

    fn try_from(value: ValType) -> Result<Self> {
        Ok(match value {
            ValType::I32 => Self::I32,
            ValType::I64 => Self::I64,
            ValType::F32 => Self::F32,
            ValType::F64 => Self::F64,
            _ => bail!("{value:?} not yet supported"),
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct FunctionType {
    parameters: Vec<ValueType>,
    results: Vec<ValueType>,
}

impl TryFrom<&FuncType> for FunctionType {
    type Error = Error;

    fn try_from(value: &FuncType) -> Result<Self> {
        Ok(Self {
            parameters: value
                .params()
                .iter()
                .map(|&v| ValueType::try_from(v))
                .collect::<Result<_>>()?,
            results: value
                .results()
                .iter()
                .map(|&v| ValueType::try_from(v))
                .collect::<Result<_>>()?,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Function(FunctionType),
    Global { ty: ValueType, mutable: bool },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Import<'a> {
    module: &'a str,
    name: &'a str,
    ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Export<'a> {
    name: &'a str,
    ty: Type,
}

#[derive(Debug, Copy, Clone)]
struct MemInfo {
    memory_size: u32,
    memory_alignment: u32,
    table_size: u32,
    table_alignment: u32,
}

impl Default for MemInfo {
    fn default() -> Self {
        Self {
            memory_size: 0,
            memory_alignment: 1,
            table_size: 0,
            table_alignment: 1,
        }
    }
}

#[derive(Debug, Default)]
struct Metadata<'a> {
    mem_info: MemInfo,
    needed_libs: Vec<&'a str>,
    needs_memory: bool,
    needs_table: bool,
    needs_stack_pointer: bool,
    needs_heap_base: bool,
    needs_heap_end: bool,
    has_start: bool,
    imports: HashSet<Import<'a>>,
    exports: HashSet<Export<'a>>,
}

enum DylinkSubsection<'a> {
    MemInfo(MemInfo),
    Needed(Vec<&'a str>),
    ExportInfo {
        name: &'a str,
        flags: u32,
    },
    ImportInfo {
        module: &'a str,
        field: &'a str,
        flags: u32,
    },
}

type DylinkSectionReader<'a> = Subsections<'a, DylinkSubsection<'a>>;

impl<'a> Subsection<'a> for DylinkSubsection<'a> {
    fn from_reader(id: u8, mut reader: BinaryReader<'a>) -> Result<Self> {
        Ok(match id {
            0 => Self::MemInfo(MemInfo {
                memory_size: reader.read_u32(),
                memory_alignment: reader.read_u32(),
                table_size: reader.read_u32(),
                table_alignment: reader.read_u32(),
            }),
            1 => Self::Needed(
                (0..reader.read_u32())
                    .map(|_| reader.read_string())
                    .collect::<Result<_>>()?,
            ),
            2 => Self::ExportInfo {
                name: reader.read_string(),
                flags: reader.read_u32(),
            },
            3 => Self::ImportInfo {
                module: reader.read_string(),
                field: reader.read_string(),
                flags: reader.read_u32(),
            },
            _ => bail!("unrecognized `dylink.0` subsection identifier: {id}"),
        })
    }
}

impl<'a> Metadata<'a> {
    fn extract(module: &'a [u8]) -> Result<Self> {
        let mut result = Self::default();
        let mut types = Vec::new();

        for payload in Parser::new(0).parse_all(module) {
            match payload? {
                Payload::CustomSection(section) if section.name() == "dylink.0" => {
                    let reader = DylinkSectionReader::new(section.data(), section.data_offset());
                    for subsection in reader {
                        match subsection? {
                            DylinkSubsection::MemInfo(info) => result.mem_info = *info,
                            DylinkSubsection::Needed(needed) => result.needed_libs = needed.clone(),
                            DylinkSubsection::ExportInfo { .. }
                            | DylinkSubsection::ImportInfo { .. } => {
                                // todo: anything we need to keep track of here?
                            }
                        }
                    }
                }

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
                                if let TypeRef::Memory(_) = import.ty {
                                    result.needs_memory = true;
                                } else {
                                    return type_error();
                                }
                            }
                            ("env", "__memory_base") => {
                                if let TypeRef::Global(GlobalType {
                                    content_type: ValType::I32,
                                    ..
                                }) = import.ty
                                {
                                    result.needs_memory = true;
                                } else {
                                    return type_error();
                                }
                            }
                            ("env", "__indirect_function_table") => {
                                if let TypeRef::Table(TableType {
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
                                if let TypeRef::Global(GlobalType {
                                    content_type: ValType::I32,
                                    ..
                                }) = import.ty
                                {
                                    result.needs_table = true;
                                } else {
                                    return type_error();
                                }
                            }
                            ("env", "__stack_pointer") => {
                                if let TypeRef::Global(GlobalType {
                                    content_type: ValType::I32,
                                    ..
                                }) = import.ty
                                {
                                    result.needs_stack_pointer = true;
                                } else {
                                    return type_error();
                                }
                            }
                            ("env", name) => {
                                if let TypeRef::Func(ty) = import.ty {
                                    result
                                        .env_imports
                                        .insert((name, FunctionType::try_from(types[*ty])?));
                                } else {
                                    return type_error();
                                }
                            }
                            ("wasi_snapshot_preview1", name) => {
                                if let TypeRef::Func(ty) = import.ty {
                                    result
                                        .wasi_imports
                                        .insert((name, FunctionType::try_from(types[*ty])?));
                                } else {
                                    return type_error();
                                }
                            }
                            ("GOT.mem", name) => {
                                if let TypeRef::Global(GlobalType {
                                    content_type: ValType::I32,
                                    ..
                                }) = import.ty
                                {
                                    match name {
                                        "__heap_base" => result.needs_heap_base = true,
                                        "__heap_end" => result.needs_heap_end = true,
                                        _ => result.memory_address_imports.insert(name),
                                    }
                                } else {
                                    return type_error();
                                }
                            }
                            ("GOT.func", name) => {
                                if let TypeRef::Global(GlobalType {
                                    content_type: ValType::I32,
                                    ..
                                }) = import.ty
                                {
                                    result.table_address_imports.insert(name)
                                } else {
                                    return type_error();
                                }
                            }
                            (module, name) => result.imports.insert(Import {
                                module,
                                name,
                                ty: match import.ty {
                                    TypeRef::Func(ty) => {
                                        Type::Function(FunctionType::try_from(types[*ty])?)
                                    }
                                    TypeRef::Global(GlobalType {
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
                        match export.name {
                            "__wasm_apply_data_relocs" => resolve.has_data_relocs = true,
                            "__wasm_call_ctors" => resolve.has_ctors = true,
                            _ => result.exports.insert(Export {
                                name: export.name,
                                ty: match export.kind {
                                    ExternalKind::Func => Type::Function(FunctionType::try_from(
                                        function_types[export.index],
                                    )?),
                                    ExternalKind::Global => {
                                        let ty = global_types[export.index];
                                        Type::Global {
                                            ty: ValueType::try_from(ty.content_type),
                                            mutable: ty.mutable,
                                        }
                                    }
                                    kind => {
                                        bail!(
                                            "unsupported export kind for {}: {kind:?}",
                                            export.name
                                        )
                                    }
                                },
                            }),
                        }
                    }
                }

                Payload::StartSection { func, .. } => result.has_start = true,

                _ => {}
            }
        }

        Ok(result)
    }
}
