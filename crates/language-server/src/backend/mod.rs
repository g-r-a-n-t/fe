use async_lsp::ClientSocket;
use driver::DriverDataBase;
use rustc_hash::FxHashSet;
use url::Url;

use crate::builtin_files::BuiltinFiles;

pub struct Backend {
    pub(super) client: ClientSocket,
    pub(super) db: DriverDataBase,
    #[allow(dead_code)] // TODO: salsa3-compatible parallelism
    pub(super) workers: tokio::runtime::Runtime,
    pub(super) builtin_files: Option<BuiltinFiles>,
    pub(super) readonly_warnings: FxHashSet<Url>,
}

impl Backend {
    pub fn new(client: ClientSocket) -> Self {
        let db = DriverDataBase::default();
        let builtin_files = BuiltinFiles::new(&db).ok();

        let workers = tokio::runtime::Builder::new_multi_thread()
            .worker_threads(1)
            .enable_all()
            .build()
            .unwrap();
        Self {
            client,
            db,
            workers,
            builtin_files,
            readonly_warnings: FxHashSet::default(),
        }
    }

    pub fn map_internal_uri_to_client(&self, uri: Url) -> Url {
        if let Some(builtins) = self.builtin_files.as_ref() {
            return builtins.map_internal_to_client(uri);
        }
        uri
    }

    pub fn map_client_uri_to_internal(&self, uri: Url) -> Url {
        if let Some(builtins) = self.builtin_files.as_ref() {
            return builtins.map_client_to_internal(uri);
        }
        uri
    }

    pub fn is_builtin_tmp_uri(&self, uri: &Url) -> bool {
        self.builtin_files
            .as_ref()
            .is_some_and(|builtins| builtins.is_tmp_uri(uri))
    }
}
