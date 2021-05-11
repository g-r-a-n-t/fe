use fe_common::diagnostics::print_diagnostics;
use fe_common::utils::ron::to_ron_string_pretty;
use fe_parser::grammar::{contracts, expressions, functions, module, types};
use fe_parser::{ParseResult, Parser};
use insta::assert_snapshot;
use serde::Serialize;

pub fn ast_string<F, T>(test_name: &str, mut parse_fn: F, src: &str) -> String
where
    F: FnMut(&mut Parser) -> ParseResult<T>,
    T: Serialize,
{
    let mut files = fe_common::files::FileStore::new();
    let id = files.add_file(test_name, src);
    let mut parser = Parser::new(src, id);

    if let Ok(ast) = parse_fn(&mut parser) {
        if !parser.diagnostics.is_empty() {
            print_diagnostics(&parser.diagnostics, &files);
            panic!("parse error");
        }
        to_ron_string_pretty(&ast).unwrap()
    } else {
        if parser.diagnostics.is_empty() {
            eprintln!("parsing failed, but no diagnostics were generated. this should be fixed.");
            let next = parser.next();
            if next.is_err() {
                eprintln!("parser is at end of file");
            } else {
                parser.error(
                    next.unwrap().span,
                    "this is the next token at time of parsing failure",
                );
                print_diagnostics(&parser.diagnostics, &files);
            }
        } else {
            print_diagnostics(&parser.diagnostics, &files);
        }
        panic!("parse failed");
    }
}

macro_rules! test_parse {
    ($name:ident, $parse_fn:expr, $src:expr) => {
        #[test]
        fn $name() {
            assert_snapshot!(ast_string(stringify!($name), $parse_fn, $src));
        }
    };
}

test_parse! { expr_call1, expressions::parse_expr, "foo()" }
test_parse! { expr_call2, expressions::parse_expr, "foo(1,2,x=3)" }
test_parse! { expr_attr1, expressions::parse_expr, "foo.bar[0][y]" }
test_parse! { expr_attr2, expressions::parse_expr, "a[x].b[y](1)" }
test_parse! { expr_num1, expressions::parse_expr, "12345" }
test_parse! { expr_num2, expressions::parse_expr, "00001" }
test_parse! { expr_hex1, expressions::parse_expr, "0xbeefbeef" }
test_parse! { expr_hex2, expressions::parse_expr, "0xFEED1234" }
test_parse! { expr_string, expressions::parse_expr, r#""hi \tmom\n""# }
test_parse! { expr_list, expressions::parse_expr, "[]" }
test_parse! { expr_list2, expressions::parse_expr, "[x, y, z,]" }
test_parse! { expr_ternary, expressions::parse_expr, "x + 1 if y + 2 else z + 3" }
test_parse! { expr_group, expressions::parse_expr, "(1 + 2) * 3" }
test_parse! { expr_tuple1, expressions::parse_expr, "(1,)" }
test_parse! { expr_tuple2, expressions::parse_expr, "(1, 2, \n 3)" }
test_parse! { expr_tuple3, expressions::parse_expr, "(1, (2 + 3), (3 * 4, 5))" }

test_parse! { ops_not, expressions::parse_expr, "x and not y" }
test_parse! { ops_math, expressions::parse_expr, "a + b * -c ** d / e % f" }
test_parse! { ops_pos, expressions::parse_expr, "+x" }
test_parse! { ops_neg, expressions::parse_expr, "-x" }
test_parse! { ops_bnot, expressions::parse_expr, "~x" }
// bitwise op precedence: shift > and > xor > or
test_parse! { ops_bit1, expressions::parse_expr, "a & b >> c" }
test_parse! { ops_bit2, expressions::parse_expr, "a ^ b & c" }
test_parse! { ops_bit3, expressions::parse_expr, "a | b ^ c" }
test_parse! { ops_shift, expressions::parse_expr, "a << b >> c" }
test_parse! { ops_bool, expressions::parse_expr, "a or b and c" }

test_parse! { stmt_assert_no_msg, functions::parse_stmt, "assert x == y" }
test_parse! { stmt_assert_msg, functions::parse_stmt, "assert x == y, z" }
test_parse! { stmt_aug_add, functions::parse_stmt, "x += y" }
test_parse! { stmt_aug_sub, functions::parse_stmt, "x -= y" }
test_parse! { stmt_aug_mul, functions::parse_stmt, "x *= y" }
test_parse! { stmt_aug_div, functions::parse_stmt, "x /= y" }
test_parse! { stmt_aug_mod, functions::parse_stmt, "x %= y" }
test_parse! { stmt_aug_and, functions::parse_stmt, "x &= y" }
test_parse! { stmt_aug_or, functions::parse_stmt, "x |= y" }
test_parse! { stmt_aug_xor, functions::parse_stmt, "x ^= y" }
test_parse! { stmt_aug_lsh, functions::parse_stmt, "x <<= y" }
test_parse! { stmt_aug_rsh, functions::parse_stmt, "x >>= y" }
test_parse! { stmt_aug_exp, functions::parse_stmt, "x **= y" }
test_parse! { stmt_emit1, functions::parse_stmt, "emit Foo()" }
test_parse! { stmt_emit2, functions::parse_stmt, "emit Foo(1, 2, x=y)" }
test_parse! { stmt_return1, functions::parse_stmt, "return" }
test_parse! { stmt_return2, functions::parse_stmt, "return x" }
test_parse! { stmt_return3, functions::parse_stmt, "return not x" }
test_parse! { stmt_revert, functions::parse_stmt, "revert" }
test_parse! { stmt_if, functions::parse_stmt, "if a:\n b" }
test_parse! { stmt_if2, functions::parse_stmt, "if a:\n b \nelif c:\n d \nelif e: \n f \nelse:\n g" }
test_parse! { stmt_while, functions::parse_stmt, "while a > 5:\n a -= 1" }
test_parse! { stmt_for, functions::parse_stmt, "for a in b[0]:\n pass" }
test_parse! { stmt_var_decl_name, functions::parse_stmt, "foo: u256" }
test_parse! { stmt_var_decl_tuple, functions::parse_stmt, "(foo, bar): (u256, u256) = (10, 10)" }
test_parse! { stmt_var_decl_tuples, functions::parse_stmt, "(a, (b, (c, d))): x" }

test_parse! { type_def, types::parse_type_def, "type X = map<address, u256>" }
test_parse! { type_name, types::parse_type_desc, "MyType" }
test_parse! { type_array, types::parse_type_desc, "address[25]" }
test_parse! { type_3d, types::parse_type_desc, "u256[4][4][4]" }
test_parse! { type_string, types::parse_type_desc, "string<100>" }
test_parse! { type_generic, types::parse_type_desc, "foo<a, b<c>, d[10]>" }
test_parse! { type_map1, types::parse_type_desc, "map<address, u256>" }
test_parse! { type_map2, types::parse_type_desc, "map<address, map<u8, u256>>" }
test_parse! { type_map3, types::parse_type_desc, "map<address, map<u8, map<u8, u8>>>" }
test_parse! { type_map4, types::parse_type_desc, "map < address , map < u8, u256 > >" }
test_parse! { type_tuple, types::parse_type_desc, "(u8, u16, address, map<u8, u8>)" }

test_parse! { fn_def, |par| functions::parse_fn_def(par, None), "def foo21(x: bool, y: address,) -> bool:\n x"}
test_parse! { event_def, types::parse_event_def, "event Foo:\n  x: address\n  idx y: u8" }

test_parse! { import_simple, module::parse_simple_import, "import foo as bar, baz, bing as bop" }
test_parse! { struct_def, types::parse_struct_def, r#"struct S:
  x: address
  pub y: u8
  const z: u8
  pub const a: map<u8, foo>
"# }

test_parse! { contract_def, contracts::parse_contract_def, r#"contract Foo:
  x: address
  pub y: u8
  pub const z: map<u8, address>
  pub def foo() -> u8:
    return 10
  event Bar:
    idx from: address
"# }

test_parse! { module_stmts, module::parse_module, r#"
import foo as bar, baz as bum

type X = map<u8, u16>

contract A:
    pub const x: u256 = 10

contract B:
    pub x: X
"# }

test_parse! { guest_book, module::parse_module, r#"
type BookMsg = bytes[100]

contract GuestBook:
    pub guest_book: map<address, BookMsg>

    event Signed:
        idx book_msg: BookMsg

    pub def sign(book_msg: BookMsg):
        self.guest_book[msg.sender] = book_msg

        emit Signed(book_msg=book_msg)

    pub def get_msg(addr: address) -> BookMsg:
        return self.guest_book[addr]
"# }

test_parse! { invalid_parse, module::parse_module, r#"
contract o
    my_sto_tuple:(u256,i32)
    pub def e->(u256,bool,address)
        m:u256=self.my_sto_tuple.m
        return
"# }
