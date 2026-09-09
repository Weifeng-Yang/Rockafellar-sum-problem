import BlockMassGraphModel
import BlockMassKernelTests
import BlockMassParameterReturn

/-!
Actual all-continuous-dual polar reduction for the fixed c0 graph.
No polar classification, annihilation, row inequality or maximality is an input
to the final theorem. Work in progress until actual compilation and audit.
-/

noncomputable section
open scoped BigOperators
open BlockMassGraphModel BlockMassRankOne

namespace BlockMassPolar

theorem coords_K_iff (k : Dual) :
    coords k ∈ BlockMassKernelTests.K ↔ k ∈ K := by
  change (BlockMassTriangular.AbsSummable (coords k) ∧ mass k = 0 ∧ r k = 0) ↔
    (mass k = 0 ∧ r k = 0)
  exact ⟨fun hk => hk.2, fun hk => ⟨coords_absSummable k, hk⟩⟩

theorem of_coords_mem_K (a : Index → ℝ) (ha : a ∈ BlockMassKernelTests.K) :
    BlockMassC0Dual.ofAbsSummable a ha.1 ∈ K := by
  apply (coords_K_iff _).mp
  simpa only [coords, BlockMassC0Dual.coordinates_ofAbsSummable] using ha

theorem h_apply_profile (i : Index) : h i = BlockMassKernel.headProfile i := by
  simpa only [h, ZeroAtInftyContinuousMap.neg_apply,
    ZeroAtInftyContinuousMap.sub_apply, BlockMassC0Dual.basis_apply,
    BlockMassKernelTests.pointMass] using (BlockMassKernelTests.headProfile_eq_pointMass i).symm

theorem annihilator_full_dual (w : Y) (hw : ∀ k ∈ K, k w = 0) :
    ∃ d : ℝ, w = d • h := by
  have hz : BlockMassKernelTests.AnnihilatesK (fun i => w i) := by
    intro a ha
    change (BlockMassC0Dual.ofAbsSummable a ha.1) w = 0
    exact hw _ (of_coords_mem_K a ha)
  obtain ⟨d, hd⟩ := BlockMassKernelTests.annihilatesK_force_head_span
    (BlockMassC0Dual.globalC0_coe w) hz
  refine ⟨d, ?_⟩
  ext i
  simpa only [ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul, h_apply_profile] using hd i

theorem K_smul (k : Dual) (hk : k ∈ K) (s : ℝ) : s • k ∈ K := by
  simp only [K, Set.mem_setOf_eq, mass_smul, r_smul, hk.1, hk.2,
    smul_zero, mul_zero, and_self]

theorem D_add_K (a k : Dual) (ha : a ∈ D) (hk : k ∈ K) : a+k ∈ D := by
  simpa only [D, Set.mem_setOf_eq, r_add, mass_add, hk.1, hk.2, add_zero] using ha

theorem L_add (a k : Dual) : L (a+k) = L a + L k := by
  ext i
  simp only [L, E_add, r_add, ZeroAtInftyContinuousMap.add_apply,
    ZeroAtInftyContinuousMap.neg_apply, ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul]
  ring

theorem L_smul (s : ℝ) (k : Dual) : L (s • k) = s • L k := by
  ext i
  simp only [L, E_smul, r_smul, ZeroAtInftyContinuousMap.add_apply,
    ZeroAtInftyContinuousMap.neg_apply, ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul]
  ring

theorem L_kernel_pair (a k : Dual) (hk : k ∈ K) : a (L k) = -k (L a) := by
  have hs := L_symmetric_work a k
  simp only [hk.1, hk.2, Pi.zero_apply, mul_zero, tsum_zero, sub_zero] at hs
  linarith

theorem K_self_work (k : Dual) (hk : k ∈ K) : k (L k) = 0 := by
  have hs := L_kernel_pair k k hk
  linarith

theorem actual_kernel_line_bracket (x : Y) (p a k : Dual) (hk : k ∈ K) (s : ℝ) :
    bracket (x,p) (L (a+s • k),a+s • k) =
      bracket (x,p) (L a,a) - s * k (x-L p) := by
  simp only [bracket, L_add, L_smul, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    map_sub, map_add, map_smul, smul_eq_mul]
  rw [L_kernel_pair p k hk, L_kernel_pair a k hk, K_self_work k hk]
  ring

theorem affine_coefficient_zero (c b : ℝ) (hn : ∀ s : ℝ, 0 ≤ c-s*b) : b=0 := by
  by_contra hb
  have h := hn ((c+1)/b)
  have heq : c-((c+1)/b)*b = (-1 : ℝ) := by
    rw [div_mul_cancel₀ _ hb]
    ring
  rw [heq] at h
  norm_num at h

theorem polar_annihilates_kernel (x : Y) (p : Dual)
    (hp : (x,p) ∈ monotonePolar graphA) : ∀ k ∈ K, k (x-L p)=0 := by
  intro k hk
  obtain ⟨a,ha⟩ := D_nonempty
  apply affine_coefficient_zero (bracket (x,p) (L a,a))
  intro s
  have hrow : (L (a+s • k),a+s • k) ∈ graphA :=
    ⟨a+s • k, D_add_K a _ ha (K_smul k hk s), rfl⟩
  have hb := hp _ hrow
  simpa only [actual_kernel_line_bracket x p a k hk s] using hb

theorem polar_point_representation (x : Y) (p : Dual)
    (hp : (x,p) ∈ monotonePolar graphA) : ∃ d : ℝ, x=L p+d • h := by
  obtain ⟨d,hd⟩ := annihilator_full_dual (x-L p) (polar_annihilates_kernel x p hp)
  refine ⟨d, ?_⟩
  have hx := sub_eq_iff_eq_add.mp hd
  simpa only [add_comm] using hx

theorem represented_bracket (x : Y) (p a : Dual) (d : ℝ) (hx : x=L p+d • h) :
    bracket (x,p) (L a,a) =
      (r a-(r p+d/2))^2-(d/2)^2-∑' b, (mass p b-mass a b)^2 := by
  rw [hx]
  calc
    bracket (L p+d • h,p) (L a,a) =
        (p-a) (L p-L a)+d*(r p-r a) := by
      simp only [bracket, ContinuousLinearMap.sub_apply, map_sub, map_add,
        map_smul, smul_eq_mul, apply_h]
      ring
    _ = _ := by rw [L_difference_work]; ring

theorem polar_actual_row_bounds (x : Y) (p : Dual) (d : ℝ)
    (hp : (x,p) ∈ monotonePolar graphA) (hx : x=L p+d • h) :
    BlockMassParameterReturn.ActualRowBounds (mass p) (r p+d/2) (d/2) := by
  intro t ht
  have hs : (L (sectionLabel t ht),sectionLabel t ht) ∈ graphA :=
    ⟨sectionLabel t ht, sectionLabel_mem_D t ht, rfl⟩
  have hrow := hp _ hs
  rw [represented_bracket x p (sectionLabel t ht) d hx,
    r_sectionLabel, mass_sectionLabel] at hrow
  linarith

theorem every_polar_point_in_graph (x : Y) (p : Dual)
    (hp : (x,p) ∈ monotonePolar graphA) : (x,p) ∈ graphA := by
  obtain ⟨d,hx⟩ := polar_point_representation x p hp
  have hm : Summable (mass p) :=
    (BlockMassTriangular.absSummable_iff_summable _).mp (mass_absSummable p)
  obtain ⟨ht,hn,heq⟩ := BlockMassParameterReturn.parameter_return
    (mass p) hm (r p+d/2) (d/2) (polar_actual_row_bounds x p d hp hx)
  have hd : d=0 := by linarith
  have hD : p ∈ D := by
    constructor
    · simpa only [hd, zero_div, add_zero] using ht
    · simpa only [hd, zero_div, add_zero] using heq
  have hxp : x=L p := by simpa only [hd, zero_smul, add_zero] using hx
  exact ⟨p,hD,Prod.ext hxp rfl⟩

theorem graphA_polar_eq : monotonePolar graphA = graphA := by
  apply Set.Subset.antisymm
  · rintro ⟨x,p⟩ hp
    exact every_polar_point_in_graph x p hp
  · exact (graphMonotone_iff_subset_polar graphA).mp graphA_monotone

theorem graphA_maximally_monotone : MaximallyMonotone graphA :=
  (maximallyMonotone_iff_polar_eq graphA).mpr graphA_polar_eq

end BlockMassPolar

#print axioms BlockMassPolar.coords_K_iff
#print axioms BlockMassPolar.of_coords_mem_K
#print axioms BlockMassPolar.annihilator_full_dual
#print axioms BlockMassPolar.actual_kernel_line_bracket
#print axioms BlockMassPolar.polar_annihilates_kernel
#print axioms BlockMassPolar.polar_point_representation
#print axioms BlockMassPolar.represented_bracket
#print axioms BlockMassPolar.polar_actual_row_bounds
#print axioms BlockMassPolar.every_polar_point_in_graph
#print axioms BlockMassPolar.graphA_polar_eq
#print axioms BlockMassPolar.graphA_maximally_monotone
