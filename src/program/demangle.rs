#[cfg(feature = "demangle")]
pub(crate) fn demangled_name(symbol: &str) -> Option<String> {
    if let Ok(name) = rustc_demangle::try_demangle(symbol) {
        return Some(format!("{name:#}"));
    }
    let itanium_symbol = symbol
        .strip_prefix('_')
        .filter(|rest| rest.starts_with("_Z"))
        .unwrap_or(symbol);
    let options = cpp_demangle::DemangleOptions::new().no_params().no_return_type();
    cpp_demangle::Symbol::new(itanium_symbol)
        .ok()?
        .demangle_with_options(&options)
        .ok()
}

#[cfg(not(feature = "demangle"))]
pub(crate) fn demangled_name(_symbol: &str) -> Option<String> {
    None
}
