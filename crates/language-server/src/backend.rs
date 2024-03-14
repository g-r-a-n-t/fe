use crate::handlers::request::{handle_goto_definition, handle_hover};

use crate::stream_buffer_until::BufferUntilStreamExt;
use crate::workspace::SyncableIngotFileContext;

use fork_stream::StreamExt as _;
use futures::stream::iter;
use futures::StreamExt;
use futures_concurrency::prelude::*;
use lsp_types::TextDocumentItem;
use salsa::{ParallelDatabase, Snapshot};
use stream_operators::StreamOps;
use tokio_stream::wrappers::{IntervalStream, UnboundedReceiverStream};

use std::sync::Arc;
use tokio::sync::RwLock;

use crate::capabilities::server_capabilities;
use crate::db::LanguageServerDatabase;

use crate::diagnostics::get_diagnostics;
use crate::globals::LANGUAGE_ID;
use crate::language_server::MessageReceivers;
use crate::workspace::{IngotFileContext, SyncableInputFile, Workspace};

use log::info;

// use tokio_stream::StreamExt;

use tower_lsp::Client;

pub struct Backend {
    pub(crate) messaging: MessageReceivers,
    pub(crate) client: Client,
    pub(crate) db: LanguageServerDatabase,
    pub(crate) workspace: Arc<RwLock<Workspace>>,
    workers: tokio::runtime::Runtime,
}

impl Backend {
    pub fn new(client: Client, messaging: MessageReceivers) -> Self {
        let db = LanguageServerDatabase::default();
        let workspace = Arc::new(RwLock::new(Workspace::default()));

        let workers = tokio::runtime::Builder::new_multi_thread()
            .worker_threads(4)
            .enable_all()
            .build()
            .unwrap();
        Self {
            messaging,
            client,
            db,
            workspace,
            workers,
        }
    }
    pub async fn handle_streams(mut self) {
        info!("setting up streams");
        let workspace = self.workspace.clone();
        let db = &mut self.db;

        let client = self.client.clone();
        let messaging = self.messaging;
        // let messaging = self.messaging.clone();
        // let messaging = messaging.read().await;

        let mut initialized_stream = messaging.initialize_stream.fuse();
        let mut shutdown_stream = messaging.shutdown_stream.fuse();
        let mut did_close_stream = messaging.did_close_stream.fuse();
        let did_change_watched_files_stream = messaging.did_change_watched_files_stream.fork();

        // let mut need_filesystem_sync = did_change_watched_files_stream
        //     .clone()
        //     .debounce_time(std::time::Duration::from_millis(500));

        let mut need_filetree_sync = did_change_watched_files_stream
            .clone()
            .map(|params| iter(params.changes.into_iter()))
            .flatten()
            .filter(|change| {
                let change_type = change.typ;
                Box::pin(async move {
                    matches!(
                        change_type,
                        lsp_types::FileChangeType::CREATED | lsp_types::FileChangeType::DELETED
                    )
                })
            });
        // .debounce_time(std::time::Duration::from_millis(50));

        let (filesystem_recently_synced_tx, filesystem_recently_synced_rx) =
            tokio::sync::mpsc::unbounded_channel::<()>();
        let filesystem_recently_synced_stream =
            UnboundedReceiverStream::new(filesystem_recently_synced_rx).fork();

        let flat_did_change_watched_files = did_change_watched_files_stream
            .map(|params| futures::stream::iter(params.changes))
            .flatten()
            .fork();

        let did_change_watched_file_stream =
            flat_did_change_watched_files.clone().filter(|change| {
                let change_type = change.typ;
                Box::pin(async move { matches!(change_type, lsp_types::FileChangeType::CHANGED) })
            });

        let did_create_watched_file_stream =
            flat_did_change_watched_files.clone().filter(|change| {
                let change_type = change.typ;
                Box::pin(async move { matches!(change_type, lsp_types::FileChangeType::CREATED) })
            });
        let did_open_stream = messaging.did_open_stream.fuse();
        let did_change_stream = messaging.did_change_stream.fuse();
        let mut change_stream = (
            // did_change_watched_file_stream.map(|change| {
            //     let uri = change.uri;
            //     let path = uri.to_file_path().unwrap();
            //     let text = std::fs::read_to_string(path).unwrap();
            //     TextDocumentItem {
            //         uri: uri.clone(),
            //         language_id: LANGUAGE_ID.to_string(),
            //         version: 0,
            //         text,
            //     }
            // }),
            // did_create_watched_file_stream.map(|change| {
            //     let uri = change.uri;
            //     let path = uri.to_file_path().unwrap();
            //     let text = std::fs::read_to_string(path).unwrap();
            //     TextDocumentItem {
            //         uri: uri.clone(),
            //         language_id: LANGUAGE_ID.to_string(),
            //         version: 0,
            //         text,
            //     }
            // }),
            did_open_stream.map(|params| TextDocumentItem {
                uri: params.text_document.uri,
                language_id: LANGUAGE_ID.to_string(),
                version: params.text_document.version,
                text: params.text_document.text,
            }),
            did_change_stream.map(|params| TextDocumentItem {
                uri: params.text_document.uri,
                language_id: LANGUAGE_ID.to_string(),
                version: params.text_document.version,
                text: params.content_changes[0].text.clone(),
            }),
        )
            .merge()
            .debounce_time(std::time::Duration::from_millis(20))
            .fuse();

        let mut hover_stream = messaging.hover_stream.fuse();
        let mut goto_definition_stream = messaging.goto_definition_stream.fuse();

        info!("streams set up, looping on them now");
        loop {
            tokio::select! {
                Some(result) = initialized_stream.next() => {
                    let (initialization_params, responder) = result;
                    info!("initializing language server!");
                    // setup workspace
                    // let workspace = self.workspace.clone();
                    let mut workspace = self.workspace.write().await;
                    let _ = workspace.set_workspace_root(
                        db,
                        initialization_params
                            .root_uri
                            .unwrap()
                            .to_file_path()
                            .ok()
                            .unwrap(),
                    );

                    let _ = workspace.sync(db);

                    let capabilities = server_capabilities();
                    let initialize_result = lsp_types::InitializeResult {
                        capabilities,
                        server_info: Some(lsp_types::ServerInfo {
                            name: String::from("fe-language-server"),
                            version: Some(String::from(env!("CARGO_PKG_VERSION"))),
                        }),
                    };
                    let _ = responder.send(Ok(initialize_result));
                }
                Some(result) = shutdown_stream.next() => {
                    let (_, responder) = result;
                    info!("shutting down language server");
                    let _ = responder.send(Ok(()));
                }
                Some(change) = need_filetree_sync.next() => {
                    let change_type = change.typ.clone();
                    let path_buf = change.uri.to_file_path().unwrap();
                    let path = path_buf.to_str().unwrap();
                    match change_type {
                        lsp_types::FileChangeType::CREATED => {
                            // let workspace = &mut workspace.write().await;
                            // workspace.sync(db).expect("Failed to sync workspace");
                            // let input = workspace
                            //     .touch_input_from_file_path(db, path)
                            //     .unwrap();

                            // let ingot = workspace
                            //     .touch_ingot_from_file_path(db, path)
                            //     .unwrap();

                            // let config_path = ingot.path(db).as_str();
                            // let mut context = workspace.ingot_context_from_config_path(db, config_path).expect("Failed to get ingot context");
                            // let files = context.files.insert(path, input);

                        }
                        lsp_types::FileChangeType::DELETED => {
                            let workspace = &mut workspace.write().await;
                            let input = workspace
                                .touch_input_from_file_path(
                                    db,
                                    path
                                )
                                .unwrap();
                            let _ = input.sync(db, None);
                        }
                        _ => {}
                    }
                }
                Some(doc) = change_stream.next() => {
                    info!("change detected: {:?}", doc.uri);
                    update_input(workspace.clone(), db, doc.clone()).await;
                    // wait 2 seconds before syncing the filesystem
                    tokio::time::sleep(std::time::Duration::from_secs(2)).await;

                    let db = db.snapshot();
                    let client = client.clone();
                    let workspace = workspace.clone();
                    self.workers.spawn(
                        async move { handle_diagnostics(client, workspace, db, doc.uri).await }
                    );
                }
                Some(params) = did_close_stream.next() => {
                    let workspace = &mut workspace.write().await;
                    let input = workspace
                        .touch_input_from_file_path(
                            db,
                            params
                                .text_document
                                .uri
                                .to_file_path()
                                .unwrap()
                                .to_str()
                                .unwrap(),
                        )
                        .unwrap();
                    let _ = input.sync(db, None);
                }
                Some((params, responder)) = hover_stream.next() => {
                    let db = db.snapshot();
                    let workspace = workspace.clone();
                    // let response = handle_hover(db, workspace, params).await;
                    let response = match self.workers.spawn(handle_hover(db, workspace, params)).await {
                        Ok(response) => response,
                        Err(e) => {
                            eprintln!("Error handling hover: {:?}", e);
                            Ok(None)
                        }
                    };
                    let _ = responder.send(response);
                }
                Some((params, responder)) = goto_definition_stream.next() => {
                    let db = db.snapshot();
                    let workspace = workspace.clone();
                    let response = match handle_goto_definition(db, workspace, params).await {
                        Ok(response) => response,
                        Err(e) => {
                            eprintln!("Error handling goto definition: {:?}", e);
                            None
                        }
                    };
                    let _ = responder.send(Ok(response));
                }
            }
            tokio::task::yield_now().await;
        }
    }
}

async fn update_input(
    workspace: Arc<RwLock<Workspace>>,
    db: &mut LanguageServerDatabase,
    path: &str,
    contents: Option<String>,
) {
    let workspace = &mut workspace.write().await;
    let input = workspace
        .touch_input_from_file_path(
            db,
            path
        )
        .unwrap();
    let _ = input.sync(db, contents);
}

async fn handle_diagnostics(
    client: Client,
    workspace: Arc<RwLock<Workspace>>,
    db: Snapshot<LanguageServerDatabase>,
    url: lsp_types::Url,
) {
    let workspace = &workspace.read().await;
    let diagnostics = get_diagnostics(&db, workspace, url.clone());

    let client = client.clone();
    let diagnostics = diagnostics
        .unwrap()
        .into_iter()
        .map(|(uri, diags)| async { client.publish_diagnostics(uri, diags, None).await })
        .collect::<Vec<_>>();

    futures::future::join_all(diagnostics).await;
}
