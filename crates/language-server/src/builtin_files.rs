use anyhow::Context;
use common::stdlib::{BUILTIN_CORE_BASE_URL, BUILTIN_STD_BASE_URL, HasBuiltinCore, HasBuiltinStd};
use driver::DriverDataBase;
use rustc_hash::FxHashMap;
use std::path::{Path, PathBuf};
use tempfile::TempDir;
use url::Url;

pub struct BuiltinFiles {
    root: TempDir,
    builtin_to_tmp: FxHashMap<Url, Url>,
    tmp_to_builtin: FxHashMap<Url, Url>,
}

impl BuiltinFiles {
    pub fn new(db: &DriverDataBase) -> anyhow::Result<Self> {
        let root = tempfile::Builder::new()
            .prefix("fe-language-server-builtin-")
            .tempdir()
            .context("create builtin temp dir")?;

        let mut this = Self {
            root,
            builtin_to_tmp: FxHashMap::default(),
            tmp_to_builtin: FxHashMap::default(),
        };

        this.materialize_builtin_ingots(db)?;
        Ok(this)
    }

    pub fn map_internal_to_client(&self, uri: Url) -> Url {
        self.builtin_to_tmp.get(&uri).cloned().unwrap_or(uri)
    }

    pub fn map_client_to_internal(&self, uri: Url) -> Url {
        if let Some(mapped) = self.tmp_to_builtin.get(&uri) {
            return mapped.clone();
        }

        // Best-effort fallback: if a client normalized the file URI differently, map by path.
        if uri.scheme() == "file"
            && let Ok(path) = uri.to_file_path()
            && let Ok(rel) = path.strip_prefix(self.root.path())
        {
            let mut components = rel.components();
            let Some(root_dir) = components.next() else {
                return uri;
            };
            let name = root_dir.as_os_str().to_string_lossy();
            let base = match name.as_ref() {
                "core" => BUILTIN_CORE_BASE_URL,
                "std" => BUILTIN_STD_BASE_URL,
                _ => return uri,
            };

            let mut rel_url_path = String::new();
            for component in components {
                if !rel_url_path.is_empty() {
                    rel_url_path.push('/');
                }
                rel_url_path.push_str(&component.as_os_str().to_string_lossy());
            }

            if let Ok(base) = Url::parse(base)
                && let Ok(builtin) = base.join(&rel_url_path)
            {
                return builtin;
            }
        }

        uri
    }

    pub fn is_tmp_uri(&self, uri: &Url) -> bool {
        if self.tmp_to_builtin.contains_key(uri) {
            return true;
        }
        uri.scheme() == "file"
            && uri
                .to_file_path()
                .is_ok_and(|path| path.starts_with(self.root.path()))
    }

    fn materialize_builtin_ingots(&mut self, db: &DriverDataBase) -> anyhow::Result<()> {
        let core = db.builtin_core();
        self.materialize_ingot(db, core, "core")
            .context("materialize builtin core")?;

        let std_ingot = db.builtin_std();
        self.materialize_ingot(db, std_ingot, "std")
            .context("materialize builtin std")?;

        Ok(())
    }

    fn materialize_ingot<'db>(
        &mut self,
        db: &'db DriverDataBase,
        ingot: common::ingot::Ingot<'db>,
        name: &str,
    ) -> anyhow::Result<()> {
        let base = match name {
            "core" => Url::parse(BUILTIN_CORE_BASE_URL).expect("builtin core url parse"),
            "std" => Url::parse(BUILTIN_STD_BASE_URL).expect("builtin std url parse"),
            _ => unreachable!("unknown builtin ingot {name}"),
        };

        let out_dir = self.root.path().join(name);

        for (url, file) in ingot.files(db).iter() {
            if url.scheme() != base.scheme() {
                continue;
            }

            let relative = url.path().trim_start_matches('/');
            if relative.is_empty() {
                continue;
            }

            let out_path = join_url_path(&out_dir, relative);
            if let Some(parent) = out_path.parent() {
                std::fs::create_dir_all(parent)
                    .with_context(|| format!("create builtin temp dir {}", parent.display()))?;
            }

            std::fs::write(&out_path, file.text(db))
                .with_context(|| format!("write builtin file {}", out_path.display()))?;
            set_readonly(&out_path)?;

            let out_url =
                Url::from_file_path(&out_path).map_err(|_| anyhow::anyhow!("bad path url"))?;

            self.builtin_to_tmp.insert(url.clone(), out_url.clone());
            self.tmp_to_builtin.insert(out_url, url.clone());
        }

        Ok(())
    }
}

fn join_url_path(base: &Path, url_path: &str) -> PathBuf {
    url_path
        .split('/')
        .filter(|part| !part.is_empty())
        .fold(base.to_path_buf(), |acc, part| acc.join(part))
}

#[cfg(unix)]
fn set_readonly(path: &Path) -> anyhow::Result<()> {
    use std::os::unix::fs::PermissionsExt;
    let mut perms = std::fs::metadata(path)
        .with_context(|| format!("read metadata {}", path.display()))?
        .permissions();
    perms.set_mode(0o444);
    std::fs::set_permissions(path, perms)
        .with_context(|| format!("set readonly perms {}", path.display()))?;
    Ok(())
}

#[cfg(not(unix))]
fn set_readonly(path: &Path) -> anyhow::Result<()> {
    let mut perms = std::fs::metadata(path)
        .with_context(|| format!("read metadata {}", path.display()))?
        .permissions();
    perms.set_readonly(true);
    std::fs::set_permissions(path, perms)
        .with_context(|| format!("set readonly perms {}", path.display()))?;
    Ok(())
}
