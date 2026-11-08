# Alg User Manual

Authors: [Aleš Bizjak](https://abizjak.github.io) and [Andrej Bauer](https://www.andrej.com/)

## Introduction

Alg is a program for enumeration of finite models of single-sorted
first-order theories. Such a theory is given by a signature (a list of
constants, operations and relations) and axioms expressed in
first-order logic. Examples of first-order theories include groups,
lattices, rings, fields, posets, graphs, and many others. Alg can do
the following:

- list or count all non-isomorphic models of a given theory,
- list or count all non-isomorphic indecomposable models of a given theory.

A model is indecomposable if it cannot be written as a non-trivial
product of two smaller models. This is only relevant for equational
theories, i.e., theories whose axioms are equations only.

Currently alg has the following limitations:

- the theory must be single-sorted,
- only unary and binary operations are accepted,
- only unary predicates and binary relations are accepted,
- it is assumed that constants denote pairwise distinct elements.

This manual describes how to use alg. For installation see the
[README](README.md).

For a quick start run

```
alg --size 8 ⟨share-folder>/theories/unital_commutative_ring.th
```

where `⟨share-folder⟩` is the folder in which the installation procedure
installed the `theories` folder. If you compiled Alg in the source folder,
the equivalent command is

```
./alg.exe --size 8 theories/unital_commutative_ring.th
```

For usage information type `alg --help` and for examples of theories
see the `theories` subdirectory.

Alg is released under the open source simplified BSD License, see the
file `COPYRIGHT.txt`.

## Input

An alg input file has extension `.th` and it describes a
first-order theory. The syntax vaguely follows the syntax of the Rocq
proof assistant. A typical input file might look like this:

```
Theory Group.
Constant 1.
Unary inv.
Binary *.
Axiom unit_left: 1 * x = x.
Axiom unit_right: x * 1 = x.
Axiom inverse_left: x * inv(x) = 1.
Axiom inverse_right: inv(x) * x = 1.
Axiom associativity: (x * y) * z = x * (y * z).
```

The file starts with an optional `Theory` declaration which
names the theory, then we have declarations of constants, unary and
binary operations, predicates and binary relations (none in the above
example), and after that there are the axioms. The precise syntax
rules are as follows.

### Comments

Comments are written as in Python, i.e., a comment begins with the
`#` symbol and includes everything up to the end of line.

### General syntactic rules

An alg input file consists of a sequence of declarations
(`Theory`, `Constant`, `Unary`, `Binary`,
`Predicate`, `Relation`) and axioms (`Axiom`,
`Theorem`). Each declaration and axiom is terminated with a
period.

### The `Theory` keyword

You may give a name to your theory with the declaration

```
Theory <theory_name>.
```

*at the beginning of the input file*, possibly preceded by
comments and whitespace. The theory name consists of letters, numbers,
and the underscore. If you do not provide a theory name, alg will
deduce one from the file name.

### Declaration of operations and relations

The declarations

```
Constant c_1 c_2 ... c_k.
Unary u_1 u_2 ... u_m.
Binary b_1 b_2 ... b_n.
Predicate p_1 p_2 ... p_l.
Relation r_1 r_2 ... r_j.
```

are used to declare constants, unary and binary operations,
predicates, and binary relations, respectively. You may declare
several constants or operations with a single declaration, or one at a
time. You may mix declarations and axioms, although it is probably a
good idea to declare the constants and operations first.

The keywords `Constants`, `Predicates` and
`Relations` are synonyms for their singular counterparts.

A constant may be any string of letters, digits and the underscore
character. In particular, a constant may consist just of digits, for
example `0` or `1`.

Predicates, relations, unary and binary operations may be strings of
letters, digits and the underscore character. For example, if we
declare

```
Unary inv.
Binary mult.
```

then we can write expressions like `mult(x, inv(y))`. It is
even possible to declare operations whose names are strings of digits,
for example:

```
Unary 3 ten.
Binary +.
Axiom: 3(3(x)) + x = ten(x).
```

Alternatively, we can use *infix* and *prefix* operators.
These follow the Ocaml rules for infix and prefix notation. An
operator is a string of symbols

```
! $ % & * + - / \ : < = > ? @ ^ | ~
```

where:

- a *prefix operator* is one that starts with `?`,
  `!` or `~`. It can be used as a unary operation.

- *infix operators* can be used as binary operations and have
  four levels of precedence, listed from lowest to highest:

  - left-associative operators starting with `=`,
    `<`, `>`, `|`, `&`, `$`
  - right-associative operators starting with `@` and `^`
  - left-associative operators starting with `+`, `-`,
    and `\`
  - left-associative operators starting with `*`, `/`, and `%`
  - right-associative operators starting with `**`.

  An operator `∘` is *left-associative* if `x ∘ y ∘ z`
  is understood as `(x ∘ y) ∘ z`, and
  *right-associative* if `x ∘ y ∘ z` is understood as
  `x ∘ (y ∘ z)`. If you look at the above list again, you will
  notice that operators have the expected precedence and
  associativity. However, if you are unsure about precedence, it is
  best to use a couple of extra parentheses.

### Axioms

An axiom has the form

```
Axiom [name]: <formula>.
```

or

```
Theorem [name]: <formula>.
```

There is no difference between an axiom and a theorem as far as alg is
concerned. A good convention is to use `Axiom` for the actual
axioms and `Theorem` for statements that are consequences of
axioms and are worth including in the theory because they make alg run
faster, see the section
[How to use alg efficiently](#how-to-use-alg-efficiently).

The optional `[name]` is a string of of letters,
digits and the underscore characters. Alg has no use for names, they
are there for the user. The `<formula>` is a
first-order formula built from the following logical operations,
listed in order of increasing precedence:

- `∀x. φ` is written as `forall x, φ`,
- `∃x. φ` is written as `exists x, φ`,
- `φ ⇔ ψ` is written as `φ <-> ψ` or `φ <=> ψ`,
- `φ ⇒ ψ` is written as `φ -> ψ` or `φ => ψ`,
- `φ ∨ ψ` is written as `φ \/ ψ` or `φ or ψ`,
- `φ ∧ ψ` is written as `φ /\ ψ` or `φ and ψ`,
- `¬φ` is written as `not φ`,
- `s = t` is written as `s = t`,
- `s ≠ t` is written as `s <> t` or `s != t`,
- `⊤` and `⊥` are written as `True` and `False`, respectively.

An iterated quantification
`∀x_1. ∀x_2. ⋯ ∀x_n. φ`
may be written as

```
forall x_1 x_2 ... x_n, φ.
```

and similarly for `∃`.

Axioms may contain free variables. Thus we can write just

```
Axiom: x + y = y + x.
```

instead of

```
Axiom: forall x y, x + y = y + x.
```

## Output

### Description of the output

The output of alg is meant to be self-explanatory. Nevertheless, here
is what the output consists of:

- Title: the name of the theory.
- Theory: the input file, which can be suppressed with
  `--no-source` command-line option.
- Models: a list of the models found. This can be
  suppressed with the `--count` command-line option. Each model
  has a name `theory_name_n_m`
  where `n` is the model size and `m` is the model sequence number. If
  the theory is equational and a model can be decomposed, a
  decomposition into indecomposable
  factors is given. Please note that in general such a decomposition
  is *not* unique. Tables of all the operations and relations are
  displayed.
- Counts: a table showing how many models of each size were found.
  If more than three sizes were considered, alg also provides a URL to
  query the counts at `http://oeis.org/`, the On-Line
  Encyclopedia of Integer Sequences.

### Available output formats

Alg supports several output formats. The default is plain text and it
is sent to the screen. You can choose one of the following formats
with the `--format` command-line option:

- `text`: the default format is plain text. Actually, it is
  not entirely plain, as it is also valid Markdown. According to
  Wikipedia, *Markdown* is a lightweight markup language, originally
  created by John Gruber and Aaron Swartz to help maximum readability
  and "publishability" of both its input and output forms.
- `html`: Hypertext Markup Language, used for web pages.
- `latex`: LaTeX format, suitable for showing
  multiplication tables in published papers.
- `json`: the JSON format, suitable for futher processing,
  as explained in the section
  [Output in JSON format for futher processing](#output-in-json-format-for-futher-processing).

If you specify an output file with the `--output` option but no
`--format`, alg guesses the correct format from the output
filename extension.

### Redirection of output to a file

By default alg prints results on the standard output. You may redirect
the output to a file with the `--output` option. If you use
`--output` without `--format`, alg tries to guess the
output format from the filename extension.

### Output in JSON format for futher processing

For further processing of output use the JSON output format by
specifying `--format json` or output to a file with the
`.json` extension.

The JSON output has one of two forms, depending on whether the
`--count` option is used. Without it, the output is a list

```
["theory_name", M_1, ..., M_n]
```

where `M_1, ..., M_n` are the models found. Each model `M_i` is
given as a dictionary which maps constants, unary operations and
binary operations, predicates and relations to the corresponding
integers, tables and matrices. For example, the only commutative ring
of size 6 with unit is presented as

```
{
  "0" : 0,
  "1" : 4,
  "~" : [0, 2, 1, 3, 5, 4],
  "+" :
    [
      [0, 1, 2, 3, 4, 5],
      [1, 2, 0, 4, 5, 3],
      [2, 0, 1, 5, 3, 4],
      [3, 4, 5, 0, 1, 2],
      [4, 5, 3, 1, 2, 0],
      [5, 3, 4, 2, 0, 1]
    ],
  "*" :
    [
      [0, 0, 0, 0, 0, 0],
      [0, 1, 2, 0, 1, 2],
      [0, 2, 1, 0, 2, 1],
      [0, 0, 0, 3, 3, 3],
      [0, 1, 2, 3, 4, 5],
      [0, 2, 1, 3, 5, 4]
    ]
}
```

The underlying set of the ring is `{0,1,2,3,4,5}`, the neutral
elements for addition and multiplication are `0` and `4`,
respectively, and the operations are given as lookup tables, for
example, `~ 1 = 2` and `4 * 3 = 3`.

The `--count` option gives JSON output

```
["theory_name", [[i_1,k_1], ..., [i_n,k_n]]]
```

which is read as saying that there are `k_j` models of size `i_j`.

In Python you can import JSON data from a file
`mystuff.json` like this:

```python
import json
with open('mystuff.json','r') as f:
    mystuff = json.load(f)
```

In Mathematica just use the `Import["mystuff.json"]`
command.

## Command-line Options

Alg is used as

```
alg --size <sizes> [options] <theory.th>
```

where `theory.th` is the input file, and the options are:

- `--size <sizes>`:
  A comma-separated list of sizes that alg should consider. You can
  also specify a size interval of the form
  `m-n`. For example, `1,2,5-8` would
  mean that we consider sizes 1, 2, 5, 6, 7, 8.
- `--count`:
  Do not print out the models, just report the counts.
- `--format <format>`:
  Output in the given format. Supported formats are `text`,
  `html`, `latex`, and `json`.
- `--indecomposable`:
  Output only indecomposable models, i.e., those that are not products
  of smaller models. Only relevant for equational theories.
- `--axiom`:
  Add an extra axiom to the theory. Use the option several times to
  add several axioms. Note that on a command-line the axiom
  should be enclosed in quotes.
- `--no-products`:
  Do not try to generate models as
  products of smaller models. Use this option if you know that a model
  cannot be a product of smaller ones. For example, a field can never
  be a product of two fields. The option is assumed if the theory
  contains predicates or relations. If all of your axioms are
  equations, then you should *not* use this option.
- `--no-source`:
  Do not include the theory in the output.
- `--output <filename>`:
  Output to the given file rather than to screen.
- `--paranoid`:
  Perform additional checks to verify that the models really satisfy
  the axioms. Use this option if you think there is a bug in alg.
- `--sat`:
  Use the alternative algorithm based on satisfying the axioms rather
  than intelligent filling-in of multiplication tables. It works well
  with theories that have predicates and relations. For theories with
  unary and binary operations the standard algorithm typically
  performs better.
- `--version`:
  Print out version information and exit.
- `--help`:
  Print help.

## How to use alg efficiently

You should always keep in mind the fact that alg performs a brute
force search with a few optimizations. In the worst case its running
time is doubly exponential in the size of the models because there are
`n^(n^2)` tables for a binary operation on a set of size `n`.

Alg contains two diffrent algorithms, the *default* and the
*alternative* one. As a rule of thumb you should use the
default algorithm, unless the signature of your theory consists mostly
of predicates and relations. In any case, since the performance is not
easily predicted, you should try both algorithms and experiment by
rewriting the theory in various equivalent ways.

### The default algorithm

The default alg algorithm is optimized for *equational* theories,
i.e., those whose axioms are equations (semigroups, monoids, groups,
rings, lattices, etc., but *not* integral domains and fields).
Alg takes advantage of commutativity, associativity and idempotent
laws, and to a smaller extent of other kinds of equational laws, such
as absorption and distributivity.

Alg performs few optimizations based on non-equational axioms. Thus
you should try to reduce their number. Furthermore, in non-equational
axioms the quantifiers should always be pushed inside as much as
possible. For example, instead of

```
Axiom: forall x, exists y, x <> 0 -> x * y = 1.
```

you should write

```
Axiom: forall x, x <> 0 -> exists y, x * y = 1.
```

The best kind of axioms are those that allow alg to immediately fill in
a whole column or row. Typically these are axioms about neutral
elements, such as `1 * x = x` and `0 + x = x`. As a rule of thumb,
every such axiom will increase the maximum manageable size by one.

In general alg performs better if it is given more axioms and
theorems, because each additional statement cuts down the
possibilities. Thus you *should* include theorems which already
follow from other axioms. For example:

- state *both* `1 * x = x` and `x * 1 = x`, even if
  one of them follows from the other,
- more generally, state all versions of a symmetric equation, even
  if they all follow from one of them,
- state laws like `0 * x = 0` (and also `x * 0 = x`), even
  if they follow from other axioms.

You should declare as many constants and as few operations as
possible. A typical example is the theory of lattices. For
*finite* structures the following are equivalent theories:

- a lattice with operations `∧`, `∨`,
- a bounded lattice with operations `∧`, `∨`
  and constants `0`, `1`,
- a `∨`-semilattice with operation `∨` and constant `0`,
- a bounded `∨`-semilattice with operation `∨`
  and constants `0`, `1`.

The best choice is the last one because it has just fewest operation and
most constants. Indeed, figuring out that there are 53 lattices of size
7 takes 250 times longer with the theory of a lattice than with the
theory of a bounded `∨`-semilattice.

Lastly, we should mention that alg generates tables in the order in
which the operations are declared. Sometimes it is much easier to
generate tables for one operation than another, so you should experiment
by switching the order of declarations. For example, the theory of a
ring works much faster if addition `+` is declared before
multiplication `*`.

### The alternative algorithm

The alternative algorithm transforms the given axioms into constraints
that need to be satisfied. It then solves the constraints in all
possible ways by intelligent backtracking. The general rules for
efficient use of the alternative algorithm are the same as those for
the default one.

It turns out that the alternative algorithm generally performs worse
than the default one when the theory consists mostly of operations.
However, the alternative algorithm usually outperforms the default one
for theories which constist mostly of relations.

## Support and bug reports

Please report bugs and ask for support at the GitHub issues page
<https://github.com/andrejbauer/alg/issues>. If you report a bug,
please include the exact version number of alg, as printed out with the
`--version` command-line option.
