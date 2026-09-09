import BlockMassGraphModel
import BlockMassWorkBound
import BlockMassSumWitness

/-!
Actual last-step witness for the sealed Y/full-dual graph.
The actual row identities, zero missing, ordered CQ, and nonmaximal sum are
proved here without first-factor maximality. No Amax theorem is asserted.
The final conditional assembler retains Amax as an explicit unpaid input.
-/

noncomputable section
open scoped BigOperators Topology

namespace BlockMassConcreteWitness

open BlockMassGraphModel BlockMassCurve BlockMassRankOne BlockMassSumWitness

/-- All values in the full continuous dual, not a chosen row selection. -/
theorem graphA_row_data (x : Y) (p : Dual) (hrow : (x, p) ∈ graphA) :
    p ∈ D ∧ x = L p := by
  obtain ⟨q, hq, he⟩ := hrow
  have hp : p = q := congrArg Prod.snd he
  have hx : x = L q := congrArg Prod.fst he
  subst p
  exact ⟨hq, hx⟩

theorem actual_ne_zero (t : ℝ) (ht : Actual t) : t ≠ 0 := by
  rcases ht with ht | ht <;> linarith

/-- No injectivity of L is needed: g(Lp)=r(p), and every actual r is nonzero. -/
theorem graphA_primal_ne_zero (x : Y) (p : Dual) (hrow : (x, p) ∈ graphA) : x ≠ 0 := by
  obtain ⟨hp, hx⟩ := graphA_row_data x p hrow
  intro hz
  have hr : r p = 0 := by rw [← g_L p, ← hx, hz, map_zero]
  exact actual_ne_zero (r p) hp.1 hr

theorem graphA_zero_row_missing (p : Dual) : ((0 : Y), p) ∉ graphA := by
  intro hp
  exact graphA_primal_ne_zero 0 p hp rfl

theorem graphA_zero_fibre_empty : {p : Dual | ((0 : Y), p) ∈ graphA} = ∅ := by
  ext p
  exact iff_false_intro (graphA_zero_row_missing p)

theorem graphA_zero_not_domain : (0 : Y) ∉ graphDomain graphA := by
  rintro ⟨p, hp⟩
  exact graphA_zero_row_missing p hp

theorem actual_sign_sq (t : ℝ) (ht : Actual t) : (Real.sign t) ^ 2 = 1 := by
  rcases ht with ht | ht
  · rw [Real.sign_of_neg (by linarith)]; norm_num
  · rw [Real.sign_of_pos (by linarith)]; norm_num

/-- Genuine square-summability justifies splitting the actual head and tail. -/
theorem wholeF_square_sum (t : ℝ) (ht : Actual t) :
    (∑' b, (wholeF t b) ^ 2) = 1 + W (|t| - 1) := by
  rw [(wholeF_sq_summable t ht).tsum_eq_zero_add]
  change (Real.sign t) ^ 2 + (∑' n, (omega (|t| - 1) n) ^ 2) = 1 + W (|t| - 1)
  rw [actual_sign_sq t ht]
  rfl

theorem actual_mass_square_sum (p : Dual) (hp : p ∈ D) :
    (∑' b, (mass p b) ^ 2) = 1 + W (|r p| - 1) := by
  rw [hp.2]
  exact wholeF_square_sum (r p) hp.1

theorem actual_label_work_identity (p : Dual) (hp : p ∈ D) :
    p (L p) + (g (L p)) ^ 2 = 2 * (r p) ^ 2 - 1 - W (|r p| - 1) := by
  rw [L_work, g_L, actual_mass_square_sum p hp]
  ring

theorem actual_row_work_identity (x : Y) (p : Dual) (hrow : (x, p) ∈ graphA) :
    p x + (g x) ^ 2 = 2 * (r p) ^ 2 - 1 - W (|r p| - 1) := by
  obtain ⟨hp, hx⟩ := graphA_row_data x p hrow
  rw [hx]
  exact actual_label_work_identity p hp

theorem actual_row_work_gt_seven_eighths (x : Y) (p : Dual)
    (hrow : (x, p) ∈ graphA) : (7 / 8 : ℝ) < p x + (g x) ^ 2 := by
  rw [actual_row_work_identity x p hrow]
  exact BlockMassWorkBound.sum_witness_work_bound (r p) (graphA_row_data x p hrow).1.1

/-- Discharges the generic work premise with the actual strict bound. -/
theorem actual_row_work_nonneg (x : Y) (p : Dual) (hrow : (x, p) ∈ graphA) :
    0 ≤ p x + (g x) ^ 2 := by
  linarith [actual_row_work_gt_seven_eighths x p hrow]

/-- This is exactly the generic same-primal graph sum, in Y times its FULL dual. -/
def actualSum : Set (Y × Dual) := graphSum graphA (rankOneGraph g)

theorem actualSum_monotone : GraphMonotone actualSum :=
  graphSum_monotone graphA (rankOneGraph g) graphA_monotone (rankOne_graph_monotone g)

theorem actualSum_self_work_gt_seven_eighths (u : Y × Dual) (hu : u ∈ actualSum) :
    (7 / 8 : ℝ) < u.2 u.1 := by
  rcases u with ⟨x, p⟩
  obtain ⟨a, b, ha, hb, hp⟩ := hu
  change p = a + b at hp
  change b = rankOne g x at hb
  rw [hp, hb, ContinuousLinearMap.add_apply, rankOne_apply_apply]
  simpa only [pow_two] using actual_row_work_gt_seven_eighths x a ha

/-- Consumer of the audited generic zero-polar implication; no Amax input. -/
theorem actualSum_zero_polar : ((0 : Y), (0 : Dual)) ∈ monotonePolar actualSum :=
  zero_polar_of_self_work actualSum (rankOne_sum_self_work graphA g actual_row_work_nonneg)

theorem actualSum_zero_nongraph : ((0 : Y), (0 : Dual)) ∉ actualSum :=
  zero_missing_from_sum graphA (rankOneGraph g) graphA_zero_not_domain

theorem actual_rankOne_domain : graphDomain (rankOneGraph g) = Set.univ :=
  rankOne_domain g

/-- The original order: dom A intersects int(dom P), not the reversed condition. -/
theorem actual_ordered_CQ :
    (graphDomain graphA ∩ interior (graphDomain (rankOneGraph g))).Nonempty :=
  rankOne_ordered_CQ graphA g graphA_nonempty

/-- Unconditional for this concrete sum. First-factor Amax is NOT used. -/
theorem actualSum_not_maximal : ¬ MaximallyMonotone actualSum :=
  nonmaximal_of_polar_nongraph actualSum (0, 0) actualSum_zero_polar actualSum_zero_nongraph

/-- Also display the actual proper monotone extension witnessing nonmaximality. -/
theorem actualSum_insert_zero_monotone :
    GraphMonotone (insert ((0 : Y), (0 : Dual)) actualSum) :=
  (graphMonotone_insert_iff actualSum_monotone (0, 0)).mpr actualSum_zero_polar

theorem actualSum_insert_zero_strict :
    actualSum ⊂ insert ((0 : Y), (0 : Dual)) actualSum := by
  exact Set.ssubset_insert actualSum_zero_nongraph

/-- Both the functional and its induced rank-one operator are genuinely nonzero. -/
theorem g_basis00 : g (BlockMassC0Dual.basis (0, 0)) = 1 := by
  simp [g_apply, BlockMassC0Dual.basis_apply, Prod.ext_iff]

theorem g_ne_zero : g ≠ 0 := by
  intro hg
  have hh := g_basis00
  rw [hg] at hh
  norm_num at hh

theorem rankOne_basis00 : rankOne g (BlockMassC0Dual.basis (0, 0)) = g := by
  rw [rankOne_apply, g_basis00, one_smul]

theorem actual_rankOne_ne_zero : rankOne g ≠ 0 := by
  intro hp
  have hh := rankOne_basis00
  rw [hp] at hh
  exact g_ne_zero hh.symm

/-- Its range is exactly the nonzero one-dimensional line generated by g. -/
theorem actual_rankOne_range :
    Set.range (rankOne g) = Set.range (fun t : ℝ => t • g) := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨g x, rfl⟩
  · rintro ⟨t, rfl⟩
    refine ⟨t • BlockMassC0Dual.basis (0, 0), ?_⟩
    rw [rankOne_smul, rankOne_basis00]

theorem actual_rankOne_positive (x : Y) : 0 ≤ rankOne g x x := by
  rw [rankOne_apply_apply]
  exact mul_self_nonneg _

theorem actual_rankOne_maximal : MaximallyMonotone (rankOneGraph g) :=
  rankOne_maximally_monotone g

/-- Conditional assembly ONLY. The sole remaining input here is explicitly Amax;
this theorem does not prove that input and is not a resolved counterexample. -/
theorem conditional_certificate (hAmax : MaximallyMonotone graphA) :
    MaximallyMonotone graphA ∧ MaximallyMonotone (rankOneGraph g) ∧
    (graphDomain graphA ∩ interior (graphDomain (rankOneGraph g))).Nonempty ∧
    GraphMonotone actualSum ∧
    ((0 : Y), (0 : Dual)) ∈ monotonePolar actualSum ∧
    ((0 : Y), (0 : Dual)) ∉ actualSum ∧ ¬ MaximallyMonotone actualSum :=
  rankOne_sum_certificate graphA g hAmax graphA_nonempty graphA_zero_not_domain
    actual_row_work_nonneg

end BlockMassConcreteWitness

#print axioms BlockMassConcreteWitness.graphA_zero_fibre_empty
#print axioms BlockMassConcreteWitness.actual_row_work_identity
#print axioms BlockMassConcreteWitness.actual_row_work_gt_seven_eighths
#print axioms BlockMassConcreteWitness.actualSum_not_maximal
#print axioms BlockMassConcreteWitness.conditional_certificate
