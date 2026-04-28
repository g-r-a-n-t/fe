pub(super) fn prefix_yul_name(name: &str) -> String {
    if name.starts_with('$') {
        sanitize_yul_ident(name)
    } else {
        format!("${}", sanitize_yul_ident(name))
    }
}

pub(super) fn sanitize_yul_ident(value: &str) -> String {
    value
        .chars()
        .map(|ch| {
            if ch.is_ascii_alphanumeric() || ch == '_' || ch == '$' {
                ch
            } else {
                '_'
            }
        })
        .collect()
}
