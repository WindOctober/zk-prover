use std::borrow::Cow;

pub fn normalize_svcomp_source(source: &str) -> Cow<'_, str> {
    let mut changed = false;
    let mut skip_error_return = false;
    let mut lines = Vec::new();

    for line in source.lines() {
        let trimmed = line.trim();

        if trimmed == "goto ERROR;" {
            let indent = line
                .split_once("goto")
                .map(|(prefix, _)| prefix)
                .unwrap_or("");
            lines.push(format!("{indent}reach_error();"));
            changed = true;
            continue;
        }

        if trimmed.starts_with("ERROR:") && trimmed.contains("reach_error()") {
            skip_error_return = true;
            changed = true;
            continue;
        }

        if skip_error_return && is_error_return(trimmed) {
            skip_error_return = false;
            changed = true;
            continue;
        }

        skip_error_return = false;
        lines.push(line.to_owned());
    }

    if !changed {
        return Cow::Borrowed(source);
    }

    let mut normalized = lines.join("\n");
    if source.ends_with('\n') {
        normalized.push('\n');
    }
    Cow::Owned(normalized)
}

fn is_error_return(line: &str) -> bool {
    matches!(line, "return (-1);" | "return -1;")
}

#[cfg(test)]
mod tests {
    use super::normalize_svcomp_source;

    #[test]
    fn rewrites_canonical_svcomp_error_label() {
        let source = r#"
int main() {
  if (x) {
    goto ERROR;
  }

  return (0);
  ERROR: {reach_error();abort();}
  return (-1);
}
"#;

        let normalized = normalize_svcomp_source(source);
        let expected = r#"
int main() {
  if (x) {
    reach_error();
  }

  return (0);
}
"#;

        assert_eq!(normalized.as_ref(), expected);
    }

    #[test]
    fn leaves_other_sources_unchanged() {
        let source = "int main() { return 0; }\n";
        let normalized = normalize_svcomp_source(source);
        assert!(matches!(normalized, std::borrow::Cow::Borrowed(_)));
        assert_eq!(normalized.as_ref(), source);
    }
}
