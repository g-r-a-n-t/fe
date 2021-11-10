use fe_common::files::FileStore;
use wasm_bindgen_test::wasm_bindgen_test;

macro_rules! test_file {
    ($name:ident) => {
        #[test]
        #[wasm_bindgen_test]
        fn $name() {
            let path = concat!("crashes/", stringify!($name), ".fe");
            let src = test_files::fixture(path);
            let mut files = FileStore::new();
            let id = files.add_file(path, src);
            fe_driver::compile(&files, id, true, true).ok();
        }
    };
}

test_file! { agroce531 }
