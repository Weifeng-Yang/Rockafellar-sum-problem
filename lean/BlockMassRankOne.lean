import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The full-continuous-dual rank-one factor (certificate_r1, C6/C10)

The ambient pair is an actual real normed space and its entire continuous dual.
Completeness is unnecessary for this factor, so all results apply to Banach spaces.
This module proves only the auxiliary factor, not a counterexample to the sum theorem.
The set-theoretic definition of maximality is absence of a proper monotone extension.
-/

noncomputable section

namespace BlockMassRankOne

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The real duality bracket in the SAME full continuous dual pair. -/
def bracket (u v : X × NormedSpace.Dual ℝ X) : ℝ :=
  (u.2 - v.2) (u.1 - v.1)

/-- All ordered pairs of actual graph points, including all dual values. -/
def GraphMonotone (G : Set (X × NormedSpace.Dual ℝ X)) : Prop :=
  ∀ u ∈ G, ∀ v ∈ G, 0 ≤ bracket u v

/-- D1: the polar quantifies over every label in the continuous dual. -/
def monotonePolar (G : Set (X × NormedSpace.Dual ℝ X)) :
    Set (X × NormedSpace.Dual ℝ X) :=
  {u | ∀ v ∈ G, 0 ≤ bracket u v}

/-- Maximality is defined by no proper monotone extension in the same ambient set. -/
def MaximallyMonotone (G : Set (X × NormedSpace.Dual ℝ X)) : Prop :=
  GraphMonotone G ∧ ∀ H : Set (X × NormedSpace.Dual ℝ X),
    G ⊆ H → GraphMonotone H → H = G

@[simp] theorem bracket_self (u : X × NormedSpace.Dual ℝ X) : bracket u u = 0 := by
  simp [bracket]

theorem bracket_symm (u v : X × NormedSpace.Dual ℝ X) : bracket u v = bracket v u := by
  simp only [bracket, ContinuousLinearMap.sub_apply, map_sub]
  ring

theorem graphMonotone_iff_subset_polar (G : Set (X × NormedSpace.Dual ℝ X)) :
    GraphMonotone G ↔ G ⊆ monotonePolar G := Iff.rfl

theorem graphMonotone_insert_iff {G : Set (X × NormedSpace.Dual ℝ X)}
    (hG : GraphMonotone G) (u : X × NormedSpace.Dual ℝ X) :
    GraphMonotone (insert u G) ↔ u ∈ monotonePolar G := by
  constructor
  · intro h v hv
    exact h u (Set.mem_insert u G) v (Set.mem_insert_of_mem u hv)
  · intro hu v hv w hw
    rcases Set.mem_insert_iff.mp hv with rfl | hvG
    · rcases Set.mem_insert_iff.mp hw with rfl | hwG
      · simp
      · exact hu w hwG
    · rcases Set.mem_insert_iff.mp hw with rfl | hwG
      · rw [bracket_symm]
        exact hu v hvG
      · exact hG v hvG w hwG

theorem maximallyMonotone_iff_polar_eq (G : Set (X × NormedSpace.Dual ℝ X)) :
    MaximallyMonotone G ↔ monotonePolar G = G := by
  constructor
  · rintro ⟨hG, hmax⟩
    apply Set.Subset.antisymm
    · intro u hu
      have hinsert := (graphMonotone_insert_iff hG u).mpr hu
      have heq := hmax (insert u G) (Set.subset_insert u G) hinsert
      rw [← heq]
      exact Set.mem_insert u G
    · exact (graphMonotone_iff_subset_polar G).mp hG
  · intro heq
    have hG : GraphMonotone G := by
      apply (graphMonotone_iff_subset_polar G).mpr
      rw [heq]
    refine ⟨hG, ?_⟩
    intro H hsub hH
    apply Set.Subset.antisymm
    · intro u hu
      rw [← heq]
      exact fun v hv => hH u hu v (hsub hv)
    · exact hsub

/-- The actual everywhere-defined bounded linear rank-one map. -/
def rankOne (g : NormedSpace.Dual ℝ X) : X →L[ℝ] NormedSpace.Dual ℝ X :=
  g.smulRight g

@[simp] theorem rankOne_apply (g : NormedSpace.Dual ℝ X) (x : X) :
    rankOne g x = (g x) • g := rfl

@[simp] theorem rankOne_apply_apply (g : NormedSpace.Dual ℝ X) (x v : X) :
    rankOne g x v = g x * g v := by simp [rankOne]

theorem rankOne_continuous (g : NormedSpace.Dual ℝ X) : Continuous (rankOne g) :=
  (rankOne g).continuous

theorem rankOne_add (g : NormedSpace.Dual ℝ X) (x y : X) :
    rankOne g (x + y) = rankOne g x + rankOne g y := (rankOne g).map_add x y

theorem rankOne_smul (g : NormedSpace.Dual ℝ X) (t : ℝ) (x : X) :
    rankOne g (t • x) = t • rankOne g x := (rankOne g).map_smul t x

theorem rankOne_norm_le (g : NormedSpace.Dual ℝ X) (x : X) :
    ‖rankOne g x‖ ≤ ‖g‖ ^ 2 * ‖x‖ := by
  calc
    ‖rankOne g x‖ = ‖g x‖ * ‖g‖ := norm_smul (g x) g
    _ ≤ (‖g‖ * ‖x‖) * ‖g‖ := mul_le_mul_of_nonneg_right (g.le_opNorm x) (norm_nonneg g)
    _ = ‖g‖ ^ 2 * ‖x‖ := by ring

theorem rankOne_opNorm_le (g : NormedSpace.Dual ℝ X) : ‖rankOne g‖ ≤ ‖g‖ ^ 2 :=
  (rankOne g).opNorm_le_bound (sq_nonneg ‖g‖) (rankOne_norm_le g)

def rankOneGraph (g : NormedSpace.Dual ℝ X) : Set (X × NormedSpace.Dual ℝ X) :=
  {u | u.2 = rankOne g u.1}

@[simp] theorem mem_rankOneGraph (g p : NormedSpace.Dual ℝ X) (x : X) :
    (x, p) ∈ rankOneGraph g ↔ p = rankOne g x := Iff.rfl

theorem rankOne_full_domain (g : NormedSpace.Dual ℝ X) :
    {x : X | ∃ p : NormedSpace.Dual ℝ X, (x, p) ∈ rankOneGraph g} = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact ⟨rankOne g x, rfl⟩

theorem rankOne_pairing_sub (g : NormedSpace.Dual ℝ X) (x y : X) :
    (rankOne g x - rankOne g y) (x - y) = (g (x - y)) ^ 2 := by
  simp only [ContinuousLinearMap.sub_apply, rankOne_apply_apply, map_sub]
  ring

theorem rankOne_graph_monotone (g : NormedSpace.Dual ℝ X) :
    GraphMonotone (rankOneGraph g) := by
  rintro ⟨x, p⟩ hp ⟨y, q⟩ hq
  change p = rankOne g x at hp
  change q = rankOne g y at hq
  change 0 ≤ (p - q) (x - y)
  rw [hp, hq, rankOne_pairing_sub]
  exact sq_nonneg _

/-- C10's full-line argument with the explicit test t = b / (c + 1).
The chosen parameter has the sign of b, hence the opposite sign to the linear
coefficient -b. No limiting step or division by c is needed, including c = 0. -/
theorem linear_coefficient_eq_zero (b c : ℝ) (hc : 0 ≤ c)
    (h : ∀ t : ℝ, 0 ≤ -t * b + t ^ 2 * c) : b = 0 := by
  have hd : 0 < c + 1 := by linarith
  have hdn : c + 1 ≠ 0 := ne_of_gt hd
  have hid : -(b / (c + 1)) * b + (b / (c + 1)) ^ 2 * c =
      -(b ^ 2) / (c + 1) ^ 2 := by
    field_simp [hdn]
    ring
  have ht := h (b / (c + 1))
  rw [hid] at ht
  have hn : 0 ≤ -(b ^ 2) := by
    simpa using (le_div_iff₀ (sq_pos_of_pos hd)).mp ht
  nlinarith [sq_nonneg b]

/-- The exact C10 polynomial, tested at the actual graph point z + t v. -/
theorem rankOne_line_bracket (g p : NormedSpace.Dual ℝ X) (z v : X) (t : ℝ) :
    (p - rankOne g (z + t • v)) (z - (z + t • v)) =
      -t * ((p - rankOne g z) v) + t ^ 2 * (g v) ^ 2 := by
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, map_sub, map_add, map_smul,
    rankOne_apply_apply, smul_eq_mul]
  ring

/-- Every direction annihilates the difference of the arbitrary polar label and P_g z. -/
theorem polar_difference_apply_eq_zero (g p : NormedSpace.Dual ℝ X) (z : X)
    (hp : (z, p) ∈ monotonePolar (rankOneGraph g)) (v : X) :
    (p - rankOne g z) v = 0 := by
  apply linear_coefficient_eq_zero _ ((g v) ^ 2) (sq_nonneg (g v))
  intro t
  have ht := hp (z + t • v, rankOne g (z + t • v)) rfl
  change 0 ≤ (p - rankOne g (z + t • v)) (z - (z + t • v)) at ht
  rwa [rankOne_line_bracket] at ht

/-- A genuine equality in the full continuous dual, by pointwise extensionality. -/
theorem polar_difference_eq_zero (g p : NormedSpace.Dual ℝ X) (z : X)
    (hp : (z, p) ∈ monotonePolar (rankOneGraph g)) : p - rankOne g z = 0 := by
  ext v
  exact polar_difference_apply_eq_zero g p z hp v

theorem rankOne_polar_mem_iff (g p : NormedSpace.Dual ℝ X) (z : X) :
    (z, p) ∈ monotonePolar (rankOneGraph g) ↔ p = rankOne g z := by
  constructor
  · intro hp
    exact sub_eq_zero.mp (polar_difference_eq_zero g p z hp)
  · intro hp
    exact (rankOne_graph_monotone g) (z, p) hp

theorem rankOne_polar_eq (g : NormedSpace.Dual ℝ X) :
    monotonePolar (rankOneGraph g) = rankOneGraph g := by
  ext u
  exact rankOne_polar_mem_iff g u.2 u.1

/-- Full-dual maximal monotonicity, with no assumed maximality or sum theorem. -/
theorem rankOne_maximally_monotone (g : NormedSpace.Dual ℝ X) :
    MaximallyMonotone (rankOneGraph g) :=
  (maximallyMonotone_iff_polar_eq (rankOneGraph g)).mpr (rankOne_polar_eq g)

/-- The explicit no-extension conclusion for MAIN's integration. -/
theorem rankOne_no_proper_monotone_extension (g : NormedSpace.Dual ℝ X)
    (H : Set (X × NormedSpace.Dual ℝ X))
    (hsub : rankOneGraph g ⊆ H) (hH : GraphMonotone H) : H = rankOneGraph g :=
  (rankOne_maximally_monotone g).2 H hsub hH

end BlockMassRankOne

#print axioms BlockMassRankOne.bracket_self
#print axioms BlockMassRankOne.bracket_symm
#print axioms BlockMassRankOne.graphMonotone_iff_subset_polar
#print axioms BlockMassRankOne.graphMonotone_insert_iff
#print axioms BlockMassRankOne.maximallyMonotone_iff_polar_eq
#print axioms BlockMassRankOne.rankOne
#print axioms BlockMassRankOne.rankOne_apply
#print axioms BlockMassRankOne.rankOne_apply_apply
#print axioms BlockMassRankOne.rankOne_continuous
#print axioms BlockMassRankOne.rankOne_add
#print axioms BlockMassRankOne.rankOne_smul
#print axioms BlockMassRankOne.rankOne_full_domain
#print axioms BlockMassRankOne.rankOne_norm_le
#print axioms BlockMassRankOne.rankOne_opNorm_le
#print axioms BlockMassRankOne.mem_rankOneGraph
#print axioms BlockMassRankOne.rankOne_pairing_sub
#print axioms BlockMassRankOne.rankOne_graph_monotone
#print axioms BlockMassRankOne.linear_coefficient_eq_zero
#print axioms BlockMassRankOne.rankOne_line_bracket
#print axioms BlockMassRankOne.polar_difference_apply_eq_zero
#print axioms BlockMassRankOne.polar_difference_eq_zero
#print axioms BlockMassRankOne.rankOne_polar_mem_iff
#print axioms BlockMassRankOne.rankOne_polar_eq
#print axioms BlockMassRankOne.rankOne_maximally_monotone
#print axioms BlockMassRankOne.rankOne_no_proper_monotone_extension
