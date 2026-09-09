import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Full-continuous-dual identification for the global c0 model.
Lean (b,n) represents source (b,n+1). All superlevel sets and sums are global.
This module is an auxiliary Banach-space bridge, not a resolution of the sum problem.
-/
noncomputable section
open Filter Topology
open scoped BigOperators ZeroAtInfty

namespace BlockMassC0Dual

abbrev Index := ℕ × ℕ
abbrev Y := C₀(Index, ℝ)

/-- Same function-level body as BlockMassTriangular.GlobalC0. -/
def GlobalC0 (x : Index → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Set.Finite {i | ε ≤ |x i|}

/-- Same function-level body as BlockMassTriangular.AbsSummable. -/
def AbsSummable (a : Index → ℝ) : Prop := Summable (fun i => |a i|)

theorem globalC0_iff_tendsto (x : Index → ℝ) :
    GlobalC0 x ↔ Tendsto x cofinite (𝓝 0) := by
  simp only [GlobalC0, Metric.tendsto_nhds, Real.dist_eq, sub_zero,
    eventually_cofinite, not_lt]

theorem globalC0_iff_zeroAtInfty (x : Index → ℝ) :
    GlobalC0 x ↔ Tendsto x (cocompact Index) (𝓝 0) := by
  rw [Filter.cocompact_eq_cofinite]
  exact globalC0_iff_tendsto x

theorem globalC0_coe (x : Y) : GlobalC0 x :=
  (globalC0_iff_zeroAtInfty x).mpr (zero_at_infty x)

def ofGlobal (x : Index → ℝ) (hx : GlobalC0 x) : Y where
  toFun := x
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := (globalC0_iff_zeroAtInfty x).mp hx

@[simp] theorem ofGlobal_apply (x : Index → ℝ) (hx : GlobalC0 x) (i : Index) :
    ofGlobal x hx i = x i := rfl

def globalModelEquiv : Y ≃ {x : Index → ℝ // GlobalC0 x} where
  toFun x := ⟨x, globalC0_coe x⟩
  invFun x := ofGlobal x.1 x.2
  left_inv x := by ext i; rfl
  right_inv x := by cases x; rfl

theorem abs_apply_le_norm (x : Y) (i : Index) : |x i| ≤ ‖x‖ :=
  x.toBCF.norm_coe_le_norm i

theorem norm_le_of_abs_le (x : Y) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, |x i| ≤ C) : ‖x‖ ≤ C :=
  (BoundedContinuousFunction.norm_le hC).mpr h

theorem finite_support_globalC0 (x : Index → ℝ) (s : Finset Index)
    (hx : ∀ i, i ∉ s → x i = 0) : GlobalC0 x := by
  intro ε hε
  apply s.finite_toSet.subset
  intro i hi
  by_contra his
  have hz := hx i his
  simp only [Set.mem_setOf_eq, hz, abs_zero] at hi
  exact (not_le_of_gt hε) hi

def finiteVector (s : Finset Index) (a : Index → ℝ) : Y :=
  ofGlobal (fun i => if i ∈ s then a i else 0)
    (finite_support_globalC0 _ s (by intro i hi; simp [hi]))

@[simp] theorem finiteVector_apply (s : Finset Index) (a : Index → ℝ) (i : Index) :
    finiteVector s a i = if i ∈ s then a i else 0 := rfl

def basis (i : Index) : Y := finiteVector {i} (fun _ => 1)

@[simp] theorem basis_apply (i j : Index) : basis i j = if j = i then 1 else 0 := by
  simp [basis]

@[simp] theorem sum_apply (s : Finset Index) (f : Index → Y) (j : Index) :
    (∑ i ∈ s, f i) j = ∑ i ∈ s, f i j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ZeroAtInftyContinuousMap.zero_apply]
  | @insert i s hi ih =>
    simp [Finset.sum_insert hi, ZeroAtInftyContinuousMap.add_apply, ih]

theorem finiteVector_eq_sum (s : Finset Index) (a : Index → ℝ) :
    finiteVector s a = ∑ i ∈ s, a i • basis i := by
  ext j
  simp [ZeroAtInftyContinuousMap.smul_apply]

/-- Coordinates of an ARBITRARY element of the full continuous dual. -/
def coordinates (p : NormedSpace.Dual ℝ Y) (i : Index) : ℝ := p (basis i)

theorem functional_finiteVector (p : NormedSpace.Dual ℝ Y)
    (s : Finset Index) (a : Index → ℝ) :
    p (finiteVector s a) = ∑ i ∈ s, a i * coordinates p i := by
  rw [finiteVector_eq_sum, map_sum]
  simp [coordinates]

def signTest (p : NormedSpace.Dual ℝ Y) (s : Finset Index) : Y :=
  finiteVector s (fun i => if 0 ≤ coordinates p i then 1 else -1)

theorem signTest_norm_le (p : NormedSpace.Dual ℝ Y) (s : Finset Index) :
    ‖signTest p s‖ ≤ 1 := by
  apply norm_le_of_abs_le _ zero_le_one
  intro i
  simp only [signTest, finiteVector_apply]
  split_ifs <;> norm_num

theorem functional_signTest (p : NormedSpace.Dual ℝ Y) (s : Finset Index) :
    p (signTest p s) = ∑ i ∈ s, |coordinates p i| := by
  rw [signTest, functional_finiteVector]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : 0 ≤ coordinates p i
  · simp [hi, abs_of_nonneg hi]
  · simp [hi, abs_of_neg (lt_of_not_ge hi)]

theorem coordinates_finite_abs_sum_le (p : NormedSpace.Dual ℝ Y) (s : Finset Index) :
    ∑ i ∈ s, |coordinates p i| ≤ ‖p‖ := by
  calc
    ∑ i ∈ s, |coordinates p i| = p (signTest p s) := (functional_signTest p s).symm
    _ ≤ |p (signTest p s)| := le_abs_self _
    _ ≤ ‖p‖ * ‖signTest p s‖ := p.le_opNorm _
    _ ≤ ‖p‖ * 1 := mul_le_mul_of_nonneg_left (signTest_norm_le p s) (norm_nonneg p)
    _ = ‖p‖ := mul_one _

theorem coordinates_absSummable (p : NormedSpace.Dual ℝ Y) :
    AbsSummable (coordinates p) := by
  exact summable_of_sum_le (fun i => abs_nonneg _) (coordinates_finite_abs_sum_le p)

theorem coordinates_tsum_abs_le (p : NormedSpace.Dual ℝ Y) :
    (∑' i, |coordinates p i|) ≤ ‖p‖ :=
  (coordinates_absSummable p).tsum_le_of_sum_le (coordinates_finite_abs_sum_le p)

/-- Uniform finite-support approximation in the actual Banach norm, over all finite sets. -/
theorem finiteVector_tendsto (x : Y) :
    Tendsto (fun s : Finset Index => finiteVector s x) atTop (𝓝 x) := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let hfinite := globalC0_coe x (ε / 2) (half_pos hε)
  refine ⟨hfinite.toFinset, ?_⟩
  intro s hs
  rw [dist_eq_norm]
  have hnorm : ‖finiteVector s x - x‖ ≤ ε / 2 := by
    apply norm_le_of_abs_le _ (le_of_lt (half_pos hε))
    intro i
    by_cases hi : i ∈ s
    · simp [ZeroAtInftyContinuousMap.sub_apply, hi, le_of_lt (half_pos hε)]
    · have hsmall : |x i| < ε / 2 := by
        apply lt_of_not_ge
        intro hlarge
        exact hi (hs (hfinite.mem_toFinset.mpr hlarge))
      simpa [ZeroAtInftyContinuousMap.sub_apply, hi] using hsmall.le
  exact hnorm.trans_lt (half_lt_self hε)

theorem basis_hasSum (x : Y) : HasSum (fun i => x i • basis i) x := by
  change Tendsto (fun s : Finset Index => ∑ i ∈ s, x i • basis i) atTop (𝓝 x)
  simpa only [← finiteVector_eq_sum] using finiteVector_tendsto x

/-- The pairing formula is DERIVED from norm approximation and continuity of p. -/
theorem functional_eq_tsum (p : NormedSpace.Dual ℝ Y) (x : Y) :
    p x = ∑' i, x i * coordinates p i := by
  have h := (basis_hasSum x).mapL p
  simpa [coordinates] using h.tsum_eq.symm

theorem pairing_summable (a : Index → ℝ) (ha : AbsSummable a) (x : Y) :
    Summable (fun i => x i * a i) := by
  apply Summable.of_norm_bounded (fun i => ‖x‖ * |a i|) (ha.mul_left ‖x‖)
  intro i
  simp only [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (abs_apply_le_norm x i) (abs_nonneg _)

theorem pairing_absSummable (a : Index → ℝ) (ha : AbsSummable a) (x : Y) :
    Summable (fun i => |x i * a i|) :=
  (summable_abs_iff).mpr (pairing_summable a ha x)

theorem pairing_bound (a : Index → ℝ) (ha : AbsSummable a) (x : Y) :
    ‖∑' i, x i * a i‖ ≤ (∑' i, |a i|) * ‖x‖ := by
  have h : ‖∑' i, x i * a i‖ ≤ ‖x‖ * (∑' i, |a i|) := by
    apply tsum_of_norm_bounded (ha.hasSum.mul_left ‖x‖)
    intro i
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_apply_le_norm x i) (abs_nonneg _)
  simpa only [mul_comm] using h

def pairingLinear (a : Index → ℝ) (ha : AbsSummable a) : Y →ₗ[ℝ] ℝ where
  toFun x := ∑' i, x i * a i
  map_add' x y := by
    simp only [ZeroAtInftyContinuousMap.add_apply, add_mul]
    exact (pairing_summable a ha x).tsum_add (pairing_summable a ha y)
  map_smul' t x := by
    simp only [ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
    exact tsum_mul_left

/-- Every actually absolutely summable coordinate family defines a continuous functional. -/
def ofAbsSummable (a : Index → ℝ) (ha : AbsSummable a) : NormedSpace.Dual ℝ Y :=
  (pairingLinear a ha).mkContinuous (∑' i, |a i|) (pairing_bound a ha)

@[simp] theorem ofAbsSummable_apply (a : Index → ℝ) (ha : AbsSummable a) (x : Y) :
    ofAbsSummable a ha x = ∑' i, x i * a i := rfl

@[simp] theorem coordinates_ofAbsSummable (a : Index → ℝ) (ha : AbsSummable a) :
    coordinates (ofAbsSummable a ha) = a := by
  funext i
  simp [coordinates, basis_apply]
  rw [tsum_eq_single i]
  · simp
  · intro j hji
    simp [hji]

theorem ofAbsSummable_coordinates (p : NormedSpace.Dual ℝ Y) :
    ofAbsSummable (coordinates p) (coordinates_absSummable p) = p := by
  ext x
  exact (functional_eq_tsum p x).symm

def fullDualEquiv : NormedSpace.Dual ℝ Y ≃ {a : Index → ℝ // AbsSummable a} where
  toFun p := ⟨coordinates p, coordinates_absSummable p⟩
  invFun a := ofAbsSummable a.1 a.2
  left_inv := ofAbsSummable_coordinates
  right_inv a := by
    apply Subtype.ext
    exact coordinates_ofAbsSummable a.1 a.2

theorem ofAbsSummable_norm_le (a : Index → ℝ) (ha : AbsSummable a) :
    ‖ofAbsSummable a ha‖ ≤ ∑' i, |a i| :=
  (ofAbsSummable a ha).opNorm_le_bound (tsum_nonneg (fun i => abs_nonneg (a i))) (pairing_bound a ha)

theorem functional_norm_eq (p : NormedSpace.Dual ℝ Y) :
    ‖p‖ = ∑' i, |coordinates p i| := by
  apply le_antisymm
  · calc
      ‖p‖ = ‖ofAbsSummable (coordinates p) (coordinates_absSummable p)‖ :=
        congrArg norm (ofAbsSummable_coordinates p).symm
      _ ≤ ∑' i, |coordinates p i| := ofAbsSummable_norm_le _ _
  · exact coordinates_tsum_abs_le p

theorem ofAbsSummable_norm_eq (a : Index → ℝ) (ha : AbsSummable a) :
    ‖ofAbsSummable a ha‖ = ∑' i, |a i| := by
  rw [functional_norm_eq, coordinates_ofAbsSummable]

/-- Complete existence and uniqueness, with absolute summability in the conclusion. -/
theorem full_dual_representation (p : NormedSpace.Dual ℝ Y) :
    ∃! a : Index → ℝ, AbsSummable a ∧ ∀ x : Y, p x = ∑' i, x i * a i := by
  refine ⟨coordinates p, ⟨coordinates_absSummable p, functional_eq_tsum p⟩, ?_⟩
  intro a ha
  have heq : ofAbsSummable a ha.1 = p := by
    ext x
    exact (ha.2 x).symm
  have hcoords := congrArg coordinates heq
  simpa only [coordinates_ofAbsSummable] using hcoords

theorem norm_eq_iSup_abs (x : Y) : ‖x‖ = ⨆ i, |x i| := by
  exact BoundedContinuousFunction.norm_eq_iSup_norm x.toBCF

example : NormedAddCommGroup Y := inferInstance
example : NormedSpace ℝ Y := inferInstance
example : CompleteSpace Y := inferInstance

end BlockMassC0Dual

#print axioms BlockMassC0Dual.globalC0_iff_zeroAtInfty
#print axioms BlockMassC0Dual.globalModelEquiv
#print axioms BlockMassC0Dual.finite_support_globalC0
#print axioms BlockMassC0Dual.coordinates_absSummable
#print axioms BlockMassC0Dual.finiteVector_tendsto
#print axioms BlockMassC0Dual.functional_eq_tsum
#print axioms BlockMassC0Dual.ofAbsSummable
#print axioms BlockMassC0Dual.fullDualEquiv
#print axioms BlockMassC0Dual.functional_norm_eq
#print axioms BlockMassC0Dual.ofAbsSummable_norm_eq
#print axioms BlockMassC0Dual.full_dual_representation
#print axioms BlockMassC0Dual.norm_eq_iSup_abs
