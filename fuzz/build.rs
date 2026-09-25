use std::path::PathBuf;

fn main() {
    let manifest = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").expect("missing manifest directory"));
    let library_directory = std::env::var("FUZZ_CPP_OUT")
        .map(PathBuf::from)
        .unwrap_or_else(|_| manifest.join("../reference/build/fuzz_cpp"));
    println!("cargo:rustc-link-search=native={}", library_directory.display());
    println!("cargo:rustc-link-lib=static=ghidra_cpp");
    println!("cargo:rustc-link-lib=dylib=stdc++");
    println!("cargo:rustc-link-lib=dylib=z");
    println!(
        "cargo:rerun-if-changed={}",
        library_directory.join("libghidra_cpp.a").display()
    );
}
