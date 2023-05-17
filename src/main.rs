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
