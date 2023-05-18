use {
    anyhow::{bail, Error, Result},
    std::collections::HashSet,
    wasmparser::{
        BinaryReader, BinaryReaderError, ExternalKind, FuncType, Parser, Payload, RefType,
        Subsection, Subsections, TableType, TypeRef, ValType,
    },
};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ValueType {
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

impl From<ValueType> for wasm_encoder::ValType {
    fn from(value: ValueType) -> Self {
        match value {
            ValueType::I32 => Self::I32,
            ValueType::I64 => Self::I64,
            ValueType::F32 => Self::F32,
            ValueType::F64 => Self::F64,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunctionType {
    pub parameters: Vec<ValueType>,
    pub results: Vec<ValueType>,
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
pub struct GlobalType {
    pub ty: ValueType,
    pub mutable: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Function(FunctionType),
    Global(GlobalType),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Import<'a> {
    pub module: &'a str,
    pub name: &'a str,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Export<'a> {
    pub name: &'a str,
    pub ty: Type,
}

#[derive(Debug, Copy, Clone)]
pub struct MemInfo {
    pub memory_size: u32,
    pub memory_alignment: u32,
    pub table_size: u32,
    pub table_alignment: u32,
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
pub struct Metadata<'a> {
    pub mem_info: MemInfo,
    pub needed_libs: Vec<&'a str>,
    pub needs_memory: bool,
    pub needs_table: bool,
    pub needs_stack_pointer: bool,
    pub needs_heap_base: bool,
    pub needs_heap_end: bool,
    pub has_data_relocs: bool,
    pub has_ctors: bool,
    pub has_start: bool,
    pub env_imports: HashSet<(&'a str, FunctionType)>,
    pub wasi_imports: HashSet<(&'a str, FunctionType)>,
    pub memory_address_imports: HashSet<&'a str>,
    pub table_address_imports: HashSet<&'a str>,
    pub imports: HashSet<Import<'a>>,
    pub exports: HashSet<Export<'a>>,
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
    Unknown(u8),
}

type DylinkSectionReader<'a> = Subsections<'a, DylinkSubsection<'a>>;

impl<'a> Subsection<'a> for DylinkSubsection<'a> {
    fn from_reader(id: u8, mut reader: BinaryReader<'a>) -> Result<Self, BinaryReaderError> {
        Ok(match id {
            0 => Self::MemInfo(MemInfo {
                memory_size: reader.read_u32()?,
                memory_alignment: reader.read_u32()?,
                table_size: reader.read_u32()?,
                table_alignment: reader.read_u32()?,
            }),
            1 => Self::Needed(
                (0..reader.read_u32()?)
                    .map(|_| reader.read_string())
                    .collect::<Result<_, _>>()?,
            ),
            2 => Self::ExportInfo {
                name: reader.read_string()?,
                flags: reader.read_u32()?,
            },
            3 => Self::ImportInfo {
                module: reader.read_string()?,
                field: reader.read_string()?,
                flags: reader.read_u32()?,
            },
            _ => Self::Unknown(id),
        })
    }
}

impl<'a> Metadata<'a> {
    pub fn extract(module: &'a [u8]) -> Result<Self> {
        let mut result = Self::default();
        let mut types = Vec::new();
        let mut function_types = Vec::new();
        let mut global_types = Vec::new();

        for payload in Parser::new(0).parse_all(module) {
            match payload? {
                Payload::CustomSection(section) if section.name() == "dylink.0" => {
                    let reader = DylinkSectionReader::new(section.data(), section.data_offset());
                    for subsection in reader {
                        match subsection? {
                            DylinkSubsection::MemInfo(info) => result.mem_info = info,
                            DylinkSubsection::Needed(needed) => result.needed_libs = needed.clone(),
                            DylinkSubsection::ExportInfo { name, flags } => {
                                // todo: anything we need to keep track of here?
                                _ = (name, flags);
                            }
                            DylinkSubsection::ImportInfo {
                                module,
                                field,
                                flags,
                            } => {
                                // todo: anything we need to keep track of here?
                                _ = (module, field, flags);
                            }
                            DylinkSubsection::Unknown(index) => {
                                bail!("unrecognized `dylink.0` subsection: {index}")
                            }
                        }
                    }
                }

                Payload::TypeSection(reader) => {
                    types = reader
                        .into_iter()
                        .map(|r| r.map(|wasmparser::Type::Func(ty)| ty))
                        .collect::<Result<Vec<_>, _>>()?;
                }

                Payload::ImportSection(reader) => {
                    for import in reader {
                        let import = import?;

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
                                if let TypeRef::Global(wasmparser::GlobalType {
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
                                if let TypeRef::Global(wasmparser::GlobalType {
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
                                if let TypeRef::Global(wasmparser::GlobalType {
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
                                    result.env_imports.insert((
                                        name,
                                        FunctionType::try_from(
                                            &types[usize::try_from(ty).unwrap()],
                                        )?,
                                    ));
                                } else {
                                    return type_error();
                                }
                            }
                            ("wasi_snapshot_preview1", name) => {
                                if let TypeRef::Func(ty) = import.ty {
                                    result.wasi_imports.insert((
                                        name,
                                        FunctionType::try_from(
                                            &types[usize::try_from(ty).unwrap()],
                                        )?,
                                    ));
                                } else {
                                    return type_error();
                                }
                            }
                            ("GOT.mem", name) => {
                                if let TypeRef::Global(wasmparser::GlobalType {
                                    content_type: ValType::I32,
                                    ..
                                }) = import.ty
                                {
                                    match name {
                                        "__heap_base" => result.needs_heap_base = true,
                                        "__heap_end" => result.needs_heap_end = true,
                                        _ => {
                                            result.memory_address_imports.insert(name);
                                        }
                                    }
                                } else {
                                    return type_error();
                                }
                            }
                            ("GOT.func", name) => {
                                if let TypeRef::Global(wasmparser::GlobalType {
                                    content_type: ValType::I32,
                                    ..
                                }) = import.ty
                                {
                                    result.table_address_imports.insert(name);
                                } else {
                                    return type_error();
                                }
                            }
                            (module, name) => {
                                result.imports.insert(Import {
                                    module,
                                    name,
                                    ty: match import.ty {
                                        TypeRef::Func(ty) => {
                                            Type::Function(FunctionType::try_from(
                                                &types[usize::try_from(ty).unwrap()],
                                            )?)
                                        }
                                        TypeRef::Global(wasmparser::GlobalType {
                                            content_type,
                                            mutable,
                                        }) => Type::Global(GlobalType {
                                            ty: ValueType::try_from(content_type)?,
                                            mutable,
                                        }),
                                        ty => {
                                            bail!(
                                                "unsupported import ty for {module}:{name}: {ty:?}"
                                            )
                                        }
                                    },
                                });
                            }
                        }
                    }
                }

                Payload::FunctionSection(reader) => {
                    for function in reader {
                        function_types.push(usize::try_from(function?).unwrap());
                    }
                }

                Payload::GlobalSection(reader) => {
                    for global in reader {
                        global_types.push(global?.ty);
                    }
                }

                Payload::ExportSection(reader) => {
                    for export in reader {
                        let export = export?;

                        match export.name {
                            "__wasm_apply_data_relocs" => result.has_data_relocs = true,
                            "__wasm_call_ctors" => result.has_ctors = true,
                            _ => {
                                result.exports.insert(Export {
                                    name: export.name,
                                    ty: match export.kind {
                                        ExternalKind::Func => {
                                            Type::Function(FunctionType::try_from(
                                                &types[function_types
                                                    [usize::try_from(export.index).unwrap()]],
                                            )?)
                                        }
                                        ExternalKind::Global => {
                                            let ty = global_types
                                                [usize::try_from(export.index).unwrap()];
                                            Type::Global(GlobalType {
                                                ty: ValueType::try_from(ty.content_type)?,
                                                mutable: ty.mutable,
                                            })
                                        }
                                        kind => {
                                            bail!(
                                                "unsupported export kind for {}: {kind:?}",
                                                export.name
                                            )
                                        }
                                    },
                                });
                            }
                        }
                    }
                }

                Payload::StartSection { .. } => result.has_start = true,

                _ => {}
            }
        }

        Ok(result)
    }
}
