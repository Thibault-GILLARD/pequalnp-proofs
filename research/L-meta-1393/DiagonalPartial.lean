import Mathlib.Data.Set.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import PEqualNP.Defs.CircuitLowerBounds
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD

namespace DiagonalBounds

variable {P L : Type*}

def increasing (A : Set P → Set L → Prop) : Prop :=
  ∀ ⦃points points' : Set P⦄ ⦃lines lines' : Set L⦄,
    points ⊆ points' → lines ⊆ lines' → A points lines → A points' lines'

def containsIncidence (I : P → L → Prop) (points : Set P) (lines : Set L) : Prop :=
  ∃ p ∈ points, ∃ l ∈ lines, I p l

def noRectangle (I : P → L → Prop) : Prop :=
  ∀ ⦃p p' l l'⦄, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')

theorem soundOffPivot {I : P → L → Prop} {A B : Set P → Set L → Prop}
    (upA : increasing A) (upB : increasing B)
    (sound : ∀ points lines, A points lines → B points lines →
      containsIncidence I points lines)
    {pivot : L} (onPivot : A ∅ {pivot}) {points : Set P} {lines : Set L}
    (avoid : ∀ p ∈ points, ¬ I p pivot) (hb : B points lines) :
    containsIncidence I points lines := by
  have hA : A points (insert pivot lines) :=
    upA (Set.empty_subset _) (by simp) onPivot
  have hB : B points (insert pivot lines) :=
    upB (fun _ h => h) (Set.subset_insert _ _) hb
  obtain ⟨p, hp, l, hl, hpl⟩ := sound _ _ hA hB
  rcases Set.mem_insert_iff.mp hl with rfl | hl
  · exact (avoid p hp hpl).elim
  · exact ⟨p, hp, l, hl, hpl⟩

theorem badPairPointOnPivot {I : P → L → Prop} {A B : Set P → Set L → Prop}
    (upA : increasing A) (upB : increasing B)
    (sound : ∀ points lines, A points lines → B points lines →
      containsIncidence I points lines)
    {pivot l : L} {p : P} (onPivot : A ∅ {pivot})
    (accepts : B {p} {l}) (nonedge : ¬ I p l) : I p pivot := by
  classical
  by_contra h
  have avoid : ∀ q ∈ ({p} : Set P), ¬ I q pivot := by
    intro q hq
    simpa only [Set.mem_singleton_iff.mp hq] using h
  have hasEdge := soundOffPivot upA upB sound onPivot avoid accepts
  apply nonedge
  simpa [containsIncidence] using hasEdge

theorem uniqueBadPointWithTwoPivots {I : P → L → Prop} {A B : Set P → Set L → Prop}
    (noRect : noRectangle I) (upA : increasing A) (upB : increasing B)
    (sound : ∀ points lines, A points lines → B points lines →
      containsIncidence I points lines)
    {l₁ l₂ : L} (distinct : l₁ ≠ l₂) (onFirst : A ∅ {l₁}) (onSecond : A ∅ {l₂})
    {p q : P} {r s : L} (acceptsP : B {p} {r}) (nonedgeP : ¬ I p r)
    (acceptsQ : B {q} {s}) (nonedgeQ : ¬ I q s) : p = q := by
  by_contra different
  apply noRect different distinct
  exact ⟨badPairPointOnPivot upA upB sound onFirst acceptsP nonedgeP,
    badPairPointOnPivot upA upB sound onSecond acceptsP nonedgeP,
    badPairPointOnPivot upA upB sound onFirst acceptsQ nonedgeQ,
    badPairPointOnPivot upA upB sound onSecond acceptsQ nonedgeQ⟩

theorem oneFactorRejectsNonneighbors {I : P → L → Prop} {A B : Set P → Set L → Prop}
    (sound : ∀ points lines, A points lines → B points lines →
      containsIncidence I points lines) (l : L) :
    ¬ A {p | ¬ I p l} {l} ∨ ¬ B {p | ¬ I p l} {l} := by
  classical
  by_cases rejectsA : ¬ A {p | ¬ I p l} {l}
  · exact Or.inl rejectsA
  · refine Or.inr fun acceptsB => ?_
    obtain ⟨p, hp, l', hl', incident⟩ := sound _ _ (not_not.mp rejectsA) acceptsB
    have eq : l' = l := Set.mem_singleton_iff.mp hl'
    exact hp (eq ▸ incident)

open scoped BigOperators

theorem orderedPairBound [DecidableEq P] [DecidableEq L]
    (points : Finset P) (lines : Finset L) (neighbors : L → Finset P)
    (noRect : noRectangle (fun p l => p ∈ neighbors l))
    (inside : ∀ l ∈ lines, neighbors l ⊆ points) :
    (∑ l ∈ lines, ((neighbors l).offDiag).card) ≤ points.offDiag.card := by
  have disjoint : (lines : Set L).PairwiseDisjoint (fun l => (neighbors l).offDiag) := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro pair hpa hpb
    obtain ⟨hxa, hya, hxy⟩ := Finset.mem_offDiag.mp hpa
    obtain ⟨hxb, hyb, _⟩ := Finset.mem_offDiag.mp hpb
    exact noRect hxy hab ⟨hxa, hxb, hya, hyb⟩
  rw [← Finset.card_biUnion disjoint]
  apply Finset.card_le_card
  intro pair membership
  obtain ⟨l, hl, he⟩ := Finset.mem_biUnion.mp membership
  obtain ⟨hp, hq, hd⟩ := Finset.mem_offDiag.mp he
  exact Finset.mem_offDiag.mpr ⟨inside l hl hp, inside l hl hq, hd⟩

private theorem offDiagCardInt [DecidableEq P] (s : Finset P) :
    (s.offDiag.card : ℤ) = (s.card : ℤ) * (s.card : ℤ) - (s.card : ℤ) := by
  have hs : s.card ≤ s.card * s.card := by
    by_cases h : s.card = 0
    · simp [h]
    · exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero h)
  rw [Finset.offDiag_card, Nat.cast_sub hs, Nat.cast_mul]

theorem degreeSumBound [DecidableEq P] [DecidableEq L]
    (points : Finset P) (lines : Finset L) (neighbors : L → Finset P)
    (noRect : noRectangle (fun p l => p ∈ neighbors l))
    (inside : ∀ l ∈ lines, neighbors l ⊆ points) :
    799 * (∑ l ∈ lines, ((neighbors l).card : ℤ)) ≤
      (points.card : ℤ) * ((points.card : ℤ) - 1) + 160000 * (lines.card : ℤ) := by
  have pairBound : (∑ l ∈ lines, ((neighbors l).offDiag.card : ℤ)) ≤
      (points.offDiag.card : ℤ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast orderedPairBound points lines neighbors noRect inside
  have tangent (l : L) : 799 * ((neighbors l).card : ℤ) ≤
      ((neighbors l).offDiag.card : ℤ) + 160000 := by
    rw [offDiagCardInt]
    nlinarith [sq_nonneg (((neighbors l).card : ℤ) - 400)]
  have summed := Finset.sum_le_sum (s := lines) (fun l _ => tangent l)
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at summed
  simp only [Finset.sum_const, nsmul_eq_mul] at summed
  rw [offDiagCardInt] at pairBound
  linarith

theorem budgetFromSupport {ambient points lines edgeCount cost : ℕ}
    (ambientBound : ambient ≤ 159601)
    (pointsBound : points ≤ ambient) (linesBound : lines ≤ ambient)
    (wireBudget : points + lines ≤ 2 * cost)
    (countByLines : 799 * (edgeCount : ℤ) ≤
      (points : ℤ) * ((points : ℤ) - 1) + 160000 * (lines : ℤ))
    (countByPoints : 799 * (edgeCount : ℤ) ≤
      (lines : ℤ) * ((lines : ℤ) - 1) + 160000 * (points : ℤ)) :
    edgeCount ≤ 400 * cost := by
  have pointsNonnegative : (0 : ℤ) ≤ (points : ℤ) := by positivity
  have linesNonnegative : (0 : ℤ) ≤ (lines : ℤ) := by positivity
  have pointsSmall : (points : ℤ) - 1 ≤ 159600 := by omega
  have linesSmall : (lines : ℤ) - 1 ≤ 159600 := by omega
  have pointProduct := mul_le_mul_of_nonneg_left pointsSmall pointsNonnegative
  have lineProduct := mul_le_mul_of_nonneg_left linesSmall linesNonnegative
  have budgetInt : (points : ℤ) + (lines : ℤ) ≤ 2 * (cost : ℤ) := by
    exact_mod_cast wireBudget
  have bound : (edgeCount : ℤ) ≤ 400 * (cost : ℤ) := by linarith
  exact_mod_cast bound

theorem graphBudget [DecidableEq P] [DecidableEq L] (I : P → L → Prop)
    [DecidableRel I] (noRect : noRectangle I)
    (points : Finset P) (lines : Finset L) {ambient cost : ℕ}
    (ambientBound : ambient ≤ 159601)
    (pointsBound : points.card ≤ ambient) (linesBound : lines.card ≤ ambient)
    (wireBudget : points.card + lines.card ≤ 2 * cost) :
    ((points ×ˢ lines).filter (fun e => I e.1 e.2)).card ≤ 400 * cost := by
  let atLine := fun l => points.filter (fun p => I p l)
  let atPoint := fun p => lines.filter (fun l => I p l)
  let edgeSet := (points ×ˢ lines).filter (fun e => I e.1 e.2)
  have countLines : edgeSet.card = ∑ l ∈ lines, (atLine l).card := by
    simp only [edgeSet, atLine, Finset.card_filter, Finset.sum_product_right]
  have countPoints : edgeSet.card = ∑ p ∈ points, (atPoint p).card := by
    simp only [edgeSet, atPoint, Finset.card_filter, Finset.sum_product]
  have noRectLine : noRectangle (fun p l => p ∈ atLine l) := by
    intro p q l r hp hl h
    exact noRect hp hl ⟨(Finset.mem_filter.mp h.1).2, (Finset.mem_filter.mp h.2.1).2,
      (Finset.mem_filter.mp h.2.2.1).2, (Finset.mem_filter.mp h.2.2.2).2⟩
  have noRectPoint : noRectangle (fun l p => l ∈ atPoint p) := by
    intro l r p q hl hp h
    exact noRect hp hl ⟨(Finset.mem_filter.mp h.1).2, (Finset.mem_filter.mp h.2.2.1).2,
      (Finset.mem_filter.mp h.2.1).2, (Finset.mem_filter.mp h.2.2.2).2⟩
  have lineSum := degreeSumBound points lines atLine noRectLine
    (fun l _ => Finset.filter_subset (fun p => I p l) points)
  have pointSum := degreeSumBound lines points atPoint noRectPoint
    (fun p _ => Finset.filter_subset (fun l => I p l) lines)
  rw [← Nat.cast_sum, ← countLines] at lineSum
  rw [← Nat.cast_sum, ← countPoints] at pointSum
  exact budgetFromSupport ambientBound pointsBound linesBound wireBudget lineSum pointSum

end DiagonalBounds

namespace WireBudget

open PEqualNP.CircuitLowerBounds

private def values (gates : List Gate) (bits : List Bool) : List Bool :=
  gates.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) bits

private theorem valuesLength (gates : List Gate) (bits : List Bool) :
    (values gates bits).length = bits.length + gates.length := by
  induction gates generalizing bits with
  | nil => simp [values]
  | cons g tail ih =>
    change (values tail (bits ++ [g.op.eval (g.inputs.map fun i => bits.getD i false)])).length =
      bits.length + (g :: tail).length
    rw [ih]
    simp
    omega

private def nextLive (g : Gate) (wire : ℕ) (live : Finset ℕ) : Finset ℕ :=
  if wire ∈ live then live.erase wire ∪ g.inputs.toFinset.filter (fun i => i < wire) else live

private theorem nextLiveBudget (g : Gate) (wire : ℕ) (live : Finset ℕ)
    (binary : g.inputs.length ≤ 2) : (nextLive g wire live).card ≤ live.card + 1 := by
  by_cases member : wire ∈ live
  · rw [nextLive, ite_eq_left member]
    have hErase := Finset.card_erase_add_one member
    have hInputs := List.toFinset_card_le g.inputs
    have hFilter := Finset.card_filter_le g.inputs.toFinset (fun i => i < wire)
    have hUnion := Finset.card_union_le (live.erase wire) (g.inputs.toFinset.filter (fun i => i < wire))
    omega
  · simp [nextLive, member]

def origins (n : ℕ) (reverseGates : List Gate) (live : Finset ℕ) : Finset ℕ :=
  match reverseGates with
  | [] => live.filter (fun i => i < n)
  | gate :: tail => origins n tail (nextLive gate (n + tail.length) live)

theorem originsBudget (n : ℕ) (reverseGates : List Gate) (live : Finset ℕ)
    (binary : ∀ g ∈ reverseGates, g.inputs.length ≤ 2) :
    (origins n reverseGates live).card ≤ live.card + reverseGates.length := by
  induction reverseGates generalizing live with
  | nil => simpa [origins] using Finset.card_filter_le live (fun i => i < n)
  | cons gate tail ih =>
    have next := nextLiveBudget gate (n + tail.length) live (binary gate (by simp))
    have rest := ih (nextLive gate (n + tail.length) live) (fun g hg => binary g (by simp [hg]))
    simp only [origins, List.length_cons]
    omega

private theorem valuesCongr (reverseGates : List Gate) {n : ℕ} (xs ys : List Bool)
    (hx : xs.length = n) (hy : ys.length = n) (live : Finset ℕ)
    (agree : ∀ i ∈ origins n reverseGates live, xs.getD i false = ys.getD i false) :
    ∀ i ∈ live, (values reverseGates.reverse xs).getD i false =
      (values reverseGates.reverse ys).getD i false := by
  induction reverseGates generalizing live with
  | nil =>
    intro i hi
    by_cases valid : i < n
    · exact agree i (Finset.mem_filter.mpr ⟨hi, valid⟩)
    · change xs.getD i false = ys.getD i false
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | cons g tail ih =>
    let wire := n + tail.length
    let us := values tail.reverse xs
    let vs := values tail.reverse ys
    have lus : us.length = wire := by simp [us, wire, valuesLength, hx]
    have lvs : vs.length = wire := by simp [vs, wire, valuesLength, hy]
    have old := ih (nextLive g wire live) agree
    intro i hi
    rw [List.reverse_cons]
    simp only [values, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (us ++ [g.op.eval (g.inputs.map fun j => us.getD j false)]).getD i false =
      (vs ++ [g.op.eval (g.inputs.map fun j => vs.getD j false)]).getD i false
    rcases lt_trichotomy i wire with below | equal | beyond
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      apply old
      unfold nextLive
      split
      · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ne_of_lt below, hi⟩)
      · exact hi
    · subst i
      have maps : g.inputs.map (fun j => us.getD j false) =
          g.inputs.map (fun j => vs.getD j false) := by
        apply List.map_congr_left
        intro j hj
        by_cases valid : j < wire
        · apply old
          rw [nextLive, ite_eq_left hi]
          exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hj, valid⟩)
        · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      rw [maps]
      rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      simp [lus, lvs]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem circuitValuesCongr (C : Circuit) {n : ℕ} (xs ys : List Bool)
    (hx : xs.length = n) (hy : ys.length = n) (live : Finset ℕ)
    (agree : ∀ i ∈ origins n C.gates.reverse live, xs.getD i false = ys.getD i false) :
    ∀ i ∈ live, (C.wires xs).getD i false = (C.wires ys).getD i false := by
  simpa [values, Circuit.wires] using valuesCongr C.gates.reverse xs ys hx hy live agree

end WireBudget

namespace DiagonalBounds

open PEqualNP.CircuitLowerBounds

private def readWire (C : Circuit) {n : ℕ} (z : Fin n → Bool) (index : ℕ) : Bool :=
  (C.wires (List.ofFn z)).getD index false

private theorem originFromChange (C : Circuit) {n : ℕ} (roots : Finset ℕ)
    (x y : Fin n → Bool) (changed : Fin n) (agree : ∀ i ≠ changed, x i = y i)
    (differs : ∃ w ∈ roots, readWire C x w ≠ readWire C y w) :
    changed.val ∈ WireBudget.origins n C.gates.reverse roots := by
  by_contra absent
  have originsAgree : ∀ i ∈ WireBudget.origins n C.gates.reverse roots,
      (List.ofFn x).getD i false = (List.ofFn y).getD i false := by
    intro i hi
    by_cases valid : i < n
    · rw [List.getD_eq_getElem _ _ (by simpa using valid),
        List.getD_eq_getElem _ _ (by simpa using valid)]
      simpa only [List.getElem_ofFn] using
        agree ⟨i, valid⟩ (fun eq => absent ((congrArg Fin.val eq) ▸ hi))
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  obtain ⟨wire, membership, different⟩ := differs
  apply different
  exact WireBudget.circuitValuesCongr C (List.ofFn x) (List.ofFn y)
    (by simp) (by simp) roots originsAgree wire membership

private def singletonInput {n : ℕ} (i : Fin n) (z : Fin n) : Bool := decide (z = i)

private def pairInput {N : ℕ} (p l : Fin N) (z : Fin (N + N)) : Bool :=
  singletonInput (Fin.castAdd N p) z || singletonInput (Fin.natAdd N l) z

private def productAt {J n : ℕ} (C : Circuit) (fa fb : Fin J → ℕ) (j : Fin J)
    (z : Fin n → Bool) : Prop := readWire C z (fa j) = true ∧ readWire C z (fb j) = true

private def roots {J : ℕ} (fa fb : Fin J → ℕ) : Finset ℕ :=
  Finset.univ.image fa ∪ Finset.univ.image fb

private theorem changedProductOrigin {J n : ℕ} (C : Circuit) (fa fb : Fin J → ℕ)
    {j : Fin J} {x y : Fin n → Bool} (changed : Fin n)
    (on : productAt C fa fb j x) (off : ¬ productAt C fa fb j y)
    (agree : ∀ i ≠ changed, x i = y i) :
    changed.val ∈ WireBudget.origins n C.gates.reverse (roots fa fb) := by
  apply originFromChange C (roots fa fb) x y changed agree
  by_cases sameA : readWire C x (fa j) = readWire C y (fa j)
  · refine ⟨fb j, Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)), ?_⟩
    intro sameB
    exact off ⟨sameA.symm.trans on.1, sameB.symm.trans on.2⟩
  · exact ⟨fa j, Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)), sameA⟩

private theorem endpointsOfAcceptedPair {N J : ℕ}
    (I : Fin N → Fin N → Prop) (C : Circuit) (fa fb : Fin J → ℕ)
    (sound : ∀ (j : Fin J) (z : Fin (N + N) → Bool), productAt C fa fb j z →
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    {p l : Fin N} {j : Fin J} (on : productAt C fa fb j (pairInput p l)) :
    p.val ∈ WireBudget.origins (N + N) C.gates.reverse (roots fa fb) ∧
    N + l.val ∈ WireBudget.origins (N + N) C.gates.reverse (roots fa fb) := by
  have offLine : ¬ productAt C fa fb j (singletonInput (Fin.natAdd N l)) := by
    intro h
    obtain ⟨q, r, _, hit, _⟩ := sound _ _ h
    have eq : (Fin.castAdd N q).val = (Fin.natAdd N l).val :=
      congrArg Fin.val (of_decide_eq_true hit)
    change q.val = N + l.val at eq
    omega
  have offPoint : ¬ productAt C fa fb j (singletonInput (Fin.castAdd N p)) := by
    intro h
    obtain ⟨q, r, _, _, hit⟩ := sound _ _ h
    have eq : (Fin.natAdd N r).val = (Fin.castAdd N p).val :=
      congrArg Fin.val (of_decide_eq_true hit)
    change N + r.val = p.val at eq
    omega
  constructor
  · exact changedProductOrigin C fa fb (Fin.castAdd N p) on offLine
      (fun i hi => by simp [pairInput, singletonInput, hi])
  · exact changedProductOrigin C fa fb (Fin.natAdd N l) on offPoint
      (fun i hi => by
        have gone : decide (i = Fin.natAdd N l) = false := decide_eq_false hi
        simp only [pairInput, singletonInput, gone, Bool.or_false])

theorem acceptedEdgesSmallSupport {N J : ℕ}
    (I : Fin N → Fin N → Prop) [DecidableRel I] (noRect : noRectangle I)
    (C : Circuit) (fa fb : Fin J → ℕ)
    (binary : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (sound : ∀ (j : Fin J) (z : Fin (N + N) → Bool), productAt C fa fb j z →
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (edges : Finset (Fin N × Fin N))
    (smallPoints : (edges.image Prod.fst).card ≤ 159601)
    (smallLines : (edges.image Prod.snd).card ≤ 159601)
    (accepted : ∀ e ∈ edges, I e.1 e.2 ∧ ∃ j, productAt C fa fb j (pairInput e.1 e.2)) :
    edges.card ≤ 400 * (C.size + J) := by
  let points : Finset (Fin N) := edges.image Prod.fst
  let lines : Finset (Fin N) := edges.image Prod.snd
  let pointCodes := points.image Fin.val
  let lineCodes := lines.image (fun l => N + l.val)
  have pointCard : pointCodes.card = points.card :=
    Finset.card_image_of_injective _ Fin.val_injective
  have lineCard : lineCodes.card = lines.card := by
    apply Finset.card_image_of_injective
    intro a b eq
    change N + a.val = N + b.val at eq
    apply Fin.val_injective
    omega
  have separate : Disjoint pointCodes lineCodes := by
    apply Finset.disjoint_left.mpr
    intro i hiP hiL
    obtain ⟨p, _, ep⟩ := Finset.mem_image.mp hiP
    obtain ⟨l, _, el⟩ := Finset.mem_image.mp hiL
    change p.val = i at ep
    change N + l.val = i at el
    omega
  have allPresent : pointCodes ∪ lineCodes ⊆ WireBudget.origins (N + N) C.gates.reverse (roots fa fb) := by
    intro i hi
    rcases Finset.mem_union.mp hi with codeAtPoint | codeAtLine
    · obtain ⟨p, pointUsed, codeEq⟩ := Finset.mem_image.mp codeAtPoint
      change p ∈ edges.image Prod.fst at pointUsed
      obtain ⟨e, he, pointEq⟩ := Finset.mem_image.mp pointUsed
      obtain ⟨_, j, hj⟩ := accepted e he
      simpa only [pointEq, codeEq] using (endpointsOfAcceptedPair I C fa fb sound hj).1
    · obtain ⟨l, lineUsed, codeEq⟩ := Finset.mem_image.mp codeAtLine
      change l ∈ edges.image Prod.snd at lineUsed
      obtain ⟨e, he, lineEq⟩ := Finset.mem_image.mp lineUsed
      obtain ⟨_, j, hj⟩ := accepted e he
      simpa only [lineEq, codeEq] using (endpointsOfAcceptedPair I C fa fb sound hj).2
  have used := Finset.card_le_card allPresent
  rw [Finset.card_union_of_disjoint separate, pointCard, lineCard] at used
  have rootBudget : (roots fa fb).card ≤ 2 * J := by
    have eachA : (Finset.univ.image fa).card ≤ J :=
      Finset.card_image_le.trans_eq (by simp)
    have eachB : (Finset.univ.image fb).card ≤ J :=
      Finset.card_image_le.trans_eq (by simp)
    have combined := Finset.card_union_le (Finset.univ.image fa) (Finset.univ.image fb)
    unfold roots
    omega
  have backwardsBudget := WireBudget.originsBudget (N + N) C.gates.reverse (roots fa fb)
    (fun g hg => binary g (List.mem_reverse.mp hg))
  rw [List.length_reverse, ← Circuit.size] at backwardsBudget
  have wireBudget : points.card + lines.card ≤ 2 * (C.size + J) := by omega
  have possible := graphBudget I noRect points lines (ambient := 159601)
    (by decide) smallPoints smallLines wireBudget
  apply le_trans (Finset.card_le_card ?_) possible
  intro e he
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨Finset.mem_image_of_mem _ he, Finset.mem_image_of_mem _ he⟩, (accepted e he).1⟩

end DiagonalBounds
