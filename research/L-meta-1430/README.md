# One NOT gate on ten five-input functions

An exhaustive SAT search found the same minimum circuit size with AND and OR gates as with AND, OR and at most one NOT gate for all ten target truth tables. CaDiCaL 1.9.5 and Glucose 4 agreed on every minimum. [P vs NP project step L-meta-1430](https://pequalnp.com/lemma#L-meta-1430)

| Truth table | AND/OR minimum | Minimum with at most one NOT |
| --- | ---: | ---: |
| `0xeee0e880` | 8 | 8 |
| `0xaaaaaaa8` | 4 | 4 |
| `0xe8e8e8a8` | 6 | 6 |
| `0xeaa8aaa8` | 7 | 7 |
| `0xeaa8e8a8` | 7 | 7 |
| `0xeaaae888` | 6 | 6 |
| `0xeac8e8c8` | 6 | 6 |
| `0xeac8eac0` | 5 | 5 |
| `0xeae8e888` | 8 | 8 |
| `0xeae8e8c0` | 8 | 8 |

The desk recorded the search outcome as `statement_seems_false`. The project's checker accepted the formal proof of the companion statement `L-meta-1429` in a local run. The proof uses the live-wire search developed for `L-meta-1007` and adapted by `ljste` for shard 16. [Lean proof in this fork](https://github.com/Thibault-GILLARD/pequalnp-proofs/blob/b5d4060032bac00a3f3f017a68038b23be8bdd2f/lean/PEqualNP/Outside/L_meta_1429.lean) · [Shard 16 proof](https://github.com/brilliant-hq/pequalnp-proofs/pull/2918)

The upstream project merged K-Yamada-2002's proof of the companion statement. [Upstream pull request](https://github.com/brilliant-hq/pequalnp-proofs/pull/2921)

## Search

For each target, the program finds an AND/OR circuit by testing increasing gate counts. It then checks every smaller gate count with NOT enabled. The SAT instance requires the selected gates to compute the target on all 32 assignments. Each truth table stores the output for assignment `x` in bit `∑ᵢ xᵢ 2ⁱ`.

For these nonconstant targets, a minimum circuit can be restricted to the gates that feed its output. Constant wires, including out-of-range reads, can be propagated. Unary AND and OR gates and binary gates with identical inputs can be replaced by their input. A NOT gate uses its first input. These simplifications preserve the function and do not increase the gate count or the number of NOT gates. Commutativity lets the encoding order the two input indices of each binary gate.

[results.json](results.json) contains a gate list for each minimum. Input wires are numbered 0 through 4, gates add wires in the order listed, and the last wire is the output.

## Reproduce

Run from this directory with Python 3. Compare the size columns. The solvers may find different circuits of the same size.

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -r requirements.txt
.venv/bin/python search.py --solver cadical195 --output /tmp/l-meta-1430-cadical.json
.venv/bin/python search.py --solver glucose4 --output /tmp/l-meta-1430-glucose.json
```
