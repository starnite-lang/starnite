// SPDX-License-Identifier: GPL-3.0-or-later
// The CSV to JSON benchmark in Rust, written the way csv_to_json.stn is: every row becomes a
// tree, and the whole tree is rendered to one string. An object is a hash map that also keeps the
// order its keys were put in, which is what a Starnite Map is; the standard library has none, so
// it is a HashMap from key to position beside a Vec of the fields.
use std::collections::HashMap;
use std::io::{Read, Write};

#[derive(Default)]
struct Fields {
    order: Vec<(String, Json)>,
    at: HashMap<String, usize>,
}

enum Json {
    Null,
    Bool(bool),
    Int(i64),
    Num(f64),
    Text(String),
    List(Vec<Json>),
    Object(Fields),
}

struct Column {
    path: Vec<String>,
    is_list: bool,
}

fn fields_of(line: &str) -> Vec<String> {
    if !line.contains('"') {
        return line.split(',').map(|s| s.to_string()).collect();
    }
    let mut out = Vec::new();
    let mut cur = String::new();
    let mut quoted = false;
    let cs: Vec<char> = line.chars().collect();
    let mut i = 0;
    while i < cs.len() {
        let c = cs[i];
        if quoted {
            if c != '"' {
                cur.push(c);
            } else if i + 1 < cs.len() && cs[i + 1] == '"' {
                cur.push(c);
                i += 1;
            } else {
                quoted = false;
            }
        } else if c == '"' {
            quoted = true;
        } else if c == ',' {
            out.push(std::mem::take(&mut cur));
        } else {
            cur.push(c);
        }
        i += 1;
    }
    out.push(cur);
    out
}

fn value_of(cell: &str) -> Json {
    let text = cell.trim();
    if text.is_empty() {
        return Json::Null;
    }
    if text == "true" || text == "false" {
        return Json::Bool(text == "true");
    }
    if let Ok(n) = text.parse::<i64>() {
        return Json::Int(n);
    }
    if let Ok(x) = text.parse::<f64>() {
        return Json::Num(x);
    }
    Json::Text(text.to_string())
}

fn column_of(name: &str) -> Column {
    let text = name.trim();
    if let Some(base) = text.strip_suffix("[]") {
        return Column { path: base.split('.').map(|s| s.to_string()).collect(), is_list: true };
    }
    Column { path: text.split('.').map(|s| s.to_string()).collect(), is_list: false }
}

fn placed(node: Json, path: &[String], at: usize, value: Json) -> Json {
    if at == path.len() {
        return value;
    }
    let mut fields = match node {
        Json::Object(existing) => existing,
        _ => Fields::default(),
    };
    let key = &path[at];
    match fields.at.get(key).copied() {
        Some(i) => {
            let child = std::mem::replace(&mut fields.order[i].1, Json::Null);
            fields.order[i].1 = placed(child, path, at + 1, value);
        }
        None => {
            fields.at.insert(key.clone(), fields.order.len());
            fields.order.push((key.clone(), placed(Json::Null, path, at + 1, value)));
        }
    }
    Json::Object(fields)
}

fn record_of(columns: &[Column], cells: &[String]) -> Json {
    let mut record = Json::Object(Fields::default());
    for (i, column) in columns.iter().enumerate() {
        let mut value = value_of(&cells[i]);
        if column.is_list {
            let joined = cells[i].split(';').collect::<Vec<_>>().join(",");
            value = Json::List(fields_of(&joined).iter().filter(|p| !p.trim().is_empty()).map(|p| value_of(p)).collect());
        }
        record = placed(record, &column.path, 0, value);
    }
    record
}

fn parse(text: &str) -> Result<Json, String> {
    let mut lines = text.lines();
    let header = lines.next().ok_or("no header line")?;
    let columns: Vec<Column> = fields_of(header).iter().map(|n| column_of(n)).collect();
    let mut records = Vec::new();
    for (i, line) in lines.enumerate() {
        if line.trim().is_empty() {
            continue;
        }
        let cells = fields_of(line);
        if cells.len() != columns.len() {
            return Err(format!("line {}: {} fields, the header has {}", i + 2, cells.len(), columns.len()));
        }
        records.push(record_of(&columns, &cells));
    }
    Ok(Json::List(records))
}

fn quoted(text: &str) -> String {
    let mut out = String::from("\"");
    for c in text.chars() {
        if c == '"' {
            out.push_str("\\\"");
        } else if c == '\\' {
            out.push_str("\\\\");
        } else {
            out.push(c);
        }
    }
    out.push('"');
    out
}

fn render(json: &Json, depth: usize) -> String {
    let pad = "  ".repeat(depth + 1);
    let close = "  ".repeat(depth);
    match json {
        Json::Null => "null".to_string(),
        Json::Bool(b) => (if *b { "true" } else { "false" }).to_string(),
        Json::Int(n) => format!("{}", n),
        Json::Num(x) => format!("{}", x),
        Json::Text(s) => quoted(s),
        Json::List(items) if items.is_empty() => "[]".to_string(),
        Json::List(items) => {
            let parts: Vec<String> = items.iter().map(|item| format!("{}{}", pad, render(item, depth + 1))).collect();
            format!("[\n{}\n{}]", parts.join(",\n"), close)
        }
        Json::Object(fields) => {
            if fields.order.is_empty() {
                return "{}".to_string();
            }
            let parts: Vec<String> = fields.order.iter().map(|(k, v)| format!("{}{}: {}", pad, quoted(k), render(v, depth + 1))).collect();
            format!("{{\n{}\n{}}}", parts.join(",\n"), close)
        }
    }
}

fn main() {
    let mut input = String::new();
    std::io::stdin().read_to_string(&mut input).unwrap();
    match parse(&input) {
        Ok(json) => {
            let mut text = render(&json, 0);
            text.push('\n');
            std::io::stdout().write_all(text.as_bytes()).unwrap();
        }
        Err(e) => println!("{}", e),
    }
}
