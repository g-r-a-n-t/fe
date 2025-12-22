use std::{path::PathBuf, process::Command, sync::OnceLock};

use tempfile::TempDir;

fn fe_binary() -> &'static PathBuf {
    static BIN: OnceLock<PathBuf> = OnceLock::new();
    BIN.get_or_init(|| {
        let cargo_exe = std::env::var("CARGO").unwrap_or_else(|_| "cargo".to_string());
        let output = Command::new(&cargo_exe)
            .args(["build", "--bin", "fe"])
            .output()
            .expect("Failed to build fe binary");

        if !output.status.success() {
            panic!(
                "Failed to build fe binary: {}",
                String::from_utf8_lossy(&output.stderr)
            );
        }

        std::env::current_exe()
            .expect("Failed to get current exe")
            .parent()
            .expect("Failed to get parent")
            .parent()
            .expect("Failed to get parent")
            .join("fe")
    })
}

fn run_fe(args: &[&str], cwd: &std::path::Path) -> (String, i32) {
    let output = Command::new(fe_binary())
        .args(args)
        .env("NO_COLOR", "1")
        .current_dir(cwd)
        .output()
        .unwrap_or_else(|_| panic!("Failed to run fe {:?}", args));

    let mut full_output = String::new();
    if !output.stdout.is_empty() {
        full_output.push_str("=== STDOUT ===\n");
        full_output.push_str(&String::from_utf8_lossy(&output.stdout));
    }
    if !output.stderr.is_empty() {
        if !full_output.is_empty() {
            full_output.push('\n');
        }
        full_output.push_str("=== STDERR ===\n");
        full_output.push_str(&String::from_utf8_lossy(&output.stderr));
    }
    let exit_code = output.status.code().unwrap_or(-1);
    full_output.push_str(&format!("\n=== EXIT CODE: {exit_code} ==="));
    (full_output, exit_code)
}

#[test]
fn new_creates_ingot_layout() {
    let tmp = TempDir::new().expect("tempdir");
    let ingot_dir = tmp.path().join("my_ingot");

    let (output, exit_code) = run_fe(&["new", ingot_dir.to_str().unwrap()], tmp.path());
    assert_eq!(exit_code, 0, "fe new failed:\n{output}");

    let fe_toml = ingot_dir.join("fe.toml");
    assert!(fe_toml.is_file(), "missing fe.toml");
    let config = std::fs::read_to_string(&fe_toml).expect("read fe.toml");
    assert!(config.contains("[ingot]"));
    assert!(config.contains("name = \"my_ingot\""));
    assert!(config.contains("version = \"0.1.0\""));

    assert!(ingot_dir.join("src").is_dir(), "missing src/");
    assert!(ingot_dir.join("src/lib.fe").is_file(), "missing src/lib.fe");
}

#[test]
fn new_allows_overriding_name_and_version() {
    let tmp = TempDir::new().expect("tempdir");
    let ingot_dir = tmp.path().join("some_dir");

    let (output, exit_code) = run_fe(
        &[
            "new",
            "--name",
            "custom_name",
            "--version",
            "9.9.9",
            ingot_dir.to_str().unwrap(),
        ],
        tmp.path(),
    );
    assert_eq!(exit_code, 0, "fe new failed:\n{output}");

    let fe_toml = ingot_dir.join("fe.toml");
    let config = std::fs::read_to_string(&fe_toml).expect("read fe.toml");
    assert!(config.contains("name = \"custom_name\""));
    assert!(config.contains("version = \"9.9.9\""));
}

#[test]
fn new_workspace_creates_workspace_config_without_hardcoded_layout() {
    let tmp = TempDir::new().expect("tempdir");
    let ws_dir = tmp.path().join("my_ws");

    let (output, exit_code) = run_fe(
        &["new", "--workspace", ws_dir.to_str().unwrap()],
        tmp.path(),
    );
    assert_eq!(exit_code, 0, "fe new --workspace failed:\n{output}");

    let fe_toml = ws_dir.join("fe.toml");
    assert!(fe_toml.is_file(), "missing workspace fe.toml");
    let config = std::fs::read_to_string(&fe_toml).expect("read workspace fe.toml");
    assert!(config.contains("[workspace]"));
    assert!(config.contains("name = \"my_ws\""));
    assert!(config.contains("members = []"));

    assert!(
        !ws_dir.join("ingots").exists(),
        "workspace new should not create an ingots/ directory"
    );
}

#[test]
fn new_adds_member_to_enclosing_workspace() {
    let tmp = TempDir::new().expect("tempdir");
    let ws_dir = tmp.path().join("ws");
    std::fs::create_dir_all(&ws_dir).expect("create ws");
    std::fs::write(
        ws_dir.join("fe.toml"),
        r#"[workspace]
name = "ws"
version = "0.1.0"
members = []
exclude = ["target"]
"#,
    )
    .expect("write fe.toml");

    let member_dir = ws_dir.join("app");
    let (output, exit_code) = run_fe(&["new", member_dir.to_str().unwrap()], tmp.path());
    assert_eq!(exit_code, 0, "fe new failed:\n{output}");

    let updated = std::fs::read_to_string(ws_dir.join("fe.toml")).expect("read updated fe.toml");
    let value: toml::Value = updated.parse().expect("parse updated workspace fe.toml");
    let workspace = value
        .get("workspace")
        .and_then(|v| v.as_table())
        .expect("workspace table");
    let members = workspace
        .get("members")
        .and_then(|v| v.as_array())
        .expect("members array");
    assert!(
        members.iter().any(|m| m.as_str() == Some("app")),
        "expected members to contain \"app\", got: {members:?}"
    );
}

#[test]
fn new_does_not_update_workspace_when_no_workspace_update_is_set() {
    let tmp = TempDir::new().expect("tempdir");
    let ws_dir = tmp.path().join("ws");
    std::fs::create_dir_all(&ws_dir).expect("create ws");
    std::fs::write(
        ws_dir.join("fe.toml"),
        r#"[workspace]
name = "ws"
version = "0.1.0"
members = []
exclude = ["target"]
"#,
    )
    .expect("write fe.toml");

    let member_dir = ws_dir.join("app");
    let (output, exit_code) = run_fe(
        &["new", "--no-workspace-update", member_dir.to_str().unwrap()],
        tmp.path(),
    );
    assert_eq!(exit_code, 0, "fe new failed:\n{output}");

    let updated = std::fs::read_to_string(ws_dir.join("fe.toml")).expect("read updated fe.toml");
    let value: toml::Value = updated.parse().expect("parse updated workspace fe.toml");
    let workspace = value
        .get("workspace")
        .and_then(|v| v.as_table())
        .expect("workspace table");
    let members = workspace
        .get("members")
        .and_then(|v| v.as_array())
        .expect("members array");
    assert!(
        members.is_empty(),
        "expected members to remain empty, got: {members:?}"
    );
}

#[test]
fn new_does_not_add_member_when_covered_by_existing_glob() {
    let tmp = TempDir::new().expect("tempdir");
    let ws_dir = tmp.path().join("ws");
    std::fs::create_dir_all(&ws_dir).expect("create ws");
    std::fs::write(
        ws_dir.join("fe.toml"),
        r#"[workspace]
name = "ws"
version = "0.1.0"
members = ["ingots/*"]
exclude = ["target"]
"#,
    )
    .expect("write fe.toml");

    let member_dir = ws_dir.join("ingots").join("app");
    let (output, exit_code) = run_fe(&["new", member_dir.to_str().unwrap()], tmp.path());
    assert_eq!(exit_code, 0, "fe new failed:\n{output}");
    assert!(
        !output.contains("Added workspace member"),
        "expected `fe new` to skip workspace update when member is covered by glob, got:\n{output}"
    );

    let updated = std::fs::read_to_string(ws_dir.join("fe.toml")).expect("read updated fe.toml");
    let value: toml::Value = updated.parse().expect("parse updated workspace fe.toml");
    let workspace = value
        .get("workspace")
        .and_then(|v| v.as_table())
        .expect("workspace table");
    let members = workspace
        .get("members")
        .and_then(|v| v.as_array())
        .expect("members array");
    assert!(
        members.iter().any(|m| m.as_str() == Some("ingots/*")),
        "expected members to retain glob entry, got: {members:?}"
    );
    assert!(
        !members.iter().any(|m| m.as_str() == Some("ingots/app")),
        "expected members not to contain explicit \"ingots/app\", got: {members:?}"
    );
}

#[test]
fn new_adds_member_to_members_main_table() {
    let tmp = TempDir::new().expect("tempdir");
    let ws_dir = tmp.path().join("ws");
    std::fs::create_dir_all(&ws_dir).expect("create ws");
    std::fs::write(
        ws_dir.join("fe.toml"),
        r#"[workspace]
name = "ws"
version = "0.1.0"
members = { main = [], dev = ["examples/*"] }
exclude = ["target"]
"#,
    )
    .expect("write fe.toml");

    let member_dir = ws_dir.join("app");
    let (output, exit_code) = run_fe(&["new", member_dir.to_str().unwrap()], tmp.path());
    assert_eq!(exit_code, 0, "fe new failed:\n{output}");

    let updated = std::fs::read_to_string(ws_dir.join("fe.toml")).expect("read updated fe.toml");
    let value: toml::Value = updated.parse().expect("parse updated workspace fe.toml");
    let workspace = value
        .get("workspace")
        .and_then(|v| v.as_table())
        .expect("workspace table");
    let members = workspace.get("members").expect("members value");
    let member_table = members.as_table().expect("members table");
    let main = member_table
        .get("main")
        .and_then(|v| v.as_array())
        .expect("members.main array");
    assert!(
        main.iter().any(|m| m.as_str() == Some("app")),
        "expected members.main to contain \"app\", got: {main:?}"
    );
}
