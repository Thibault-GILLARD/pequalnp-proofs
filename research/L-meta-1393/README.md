# A finite-support bound for L-meta-1393

The Lean theorem `DiagonalBounds.acceptedEdgesSmallSupport` bounds the number of accepted incidences by `400 * (C.size + J)` when the accepted incidences use at most 159,601 distinct points and at most 159,601 distinct lines. It uses the fan-in and soundness assumptions of the posted task. The proof allows arbitrary line-degree and counts every incident pair accepted by a product on the two corresponding inputs. [Project step L-meta-1393](https://pequalnp.com/lemma#L-meta-1393)

## Argument

Let `m` be the number of accepted pairs and let `p` and `l` be the sizes of their point and line supports.

1. For each counted pair, a product of two wires fires when the point and line are set. Soundness makes the product false if either input is removed, since a singleton input contains no incidence. Both inputs therefore occur in the backward dependency set of the product factors.
2. The backward dependency calculation starts at at most `2 * J` factor wires. Each gate replaces one live wire with at most two earlier wires. Thus `p + l ≤ C.size + 2 * J`.
3. A pair of distinct points appears on at most one line. This bounds the sum of `d * (d - 1)` over line degrees by `p * (p - 1)`. Using `(d - 400)^2 ≥ 0` gives `799 * m ≤ p * (p - 1) + 160000 * l`. Counting in the other direction gives `799 * m ≤ l * (l - 1) + 160000 * p`.
4. The two support caps give `2 * 799 * m ≤ 319600 * (p + l)`. Hence `m ≤ 200 * (p + l) ≤ 400 * (C.size + J)`.

The file also proves a pivot observation. If one monotone factor fires on a single line, its partner is sound on assignments that contain none of the points incident with that line. If the first factor fires on two distinct single lines, all nonincident single-pair assignments accepted by its partner share at most one point endpoint.

For the unrestricted statement, a remaining case is a family of products whose two factors are individually unsound. The existing degree-two bound applies to the products with an individually sound factor, by selecting one such factor per product. [Checked degree-two bound](https://pequalnp.com/lemma#L-meta-1382)

## Check

Run from the repository's `lean` directory with the pinned Lean toolchain and Mathlib cache.

```sh
lake build +PEqualNP.Defs.CircuitLowerBounds
lake env lean ../research/L-meta-1393/DiagonalPartial.lean
```
