import BlockMassTriangular
import BlockMassKernel

/-!
Actual finite-difference tests in the full l1 kernel.

The index (b,n) represents frozen source (b,n+1). No finite-support
restriction is imposed in K. The three test families are proved members of K.
The global-c0 classification is imported from the read-only MAIN module.
-/

noncomputable section

open scoped BigOperators
open BlockMassTriangular

namespace BlockMassKernelTests

abbrev Index := BlockMassTriangular.Index

/-- Frozen r, with the positive source index shifted by one. -/
def r (k : Index → ℝ) : ℝ := -k (0, 0) - k (0, 1)

/-- The full absolutely summable kernel, not just its finite-support part. -/
def K : Set (Index → ℝ) := {k | AbsSummable k ∧ m k = 0 ∧ r k = 0}

def AnnihilatesK (z : Index → ℝ) : Prop :=
  ∀ k : Index → ℝ, k ∈ K → pairing z k = 0

def pointMass (i : Index) (p : Index) : ℝ := if p = i then 1 else 0

def difference (i j : Index) (p : Index) : ℝ := pointMass i p - pointMass j p

theorem pointMass_finite_support (i : Index) : (Function.support (pointMass i)).Finite := by
  apply (Set.finite_singleton i).subset
  intro p hp
  by_contra h
  have hi : p ≠ i := h
  exact hp (by simp [pointMass, hi])

theorem pointMass_absSummable (i : Index) : AbsSummable (pointMass i) :=
  (summable_of_finite_support (pointMass_finite_support i)).abs

theorem difference_finite_support (i j : Index) :
    (Function.support (difference i j)).Finite := by
  apply ((Set.finite_singleton i).union (Set.finite_singleton j)).subset
  intro p hp
  by_contra h
  have hi : p ≠ i := by intro hi; exact h (Or.inl hi)
  have hj : p ≠ j := by intro hj; exact h (Or.inr hj)
  exact hp (by simp [difference, pointMass, hi, hj])

theorem difference_absSummable (i j : Index) : AbsSummable (difference i j) :=
  (summable_of_finite_support (difference_finite_support i j)).abs

theorem pointMass_pairing_summable (z : Index → ℝ) (i : Index) :
    Summable (fun p => z p * pointMass i p) := by
  apply summable_of_finite_support
  apply (Set.finite_singleton i).subset
  intro p hp
  by_contra h
  have hi : p ≠ i := h
  exact hp (by simp [pointMass, hi])

theorem pairing_pointMass (z : Index → ℝ) (i : Index) :
    pairing z (pointMass i) = z i := by
  unfold pairing
  rw [tsum_eq_single i (by intro p hp; simp [pointMass, hp])]
  simp [pointMass]

theorem pairing_difference (z : Index → ℝ) (i j : Index) :
    pairing z (difference i j) = z i - z j := by
  simp only [pairing, difference, mul_sub]
  rw [(pointMass_pairing_summable z i).tsum_sub (pointMass_pairing_summable z j)]
  exact congrArg₂ (· - ·) (pairing_pointMass z i) (pairing_pointMass z j)

theorem m_pointMass (i : Index) (b : ℕ) :
    m (pointMass i) b = if b = i.1 then 1 else 0 := by
  rcases i with ⟨c, j⟩
  by_cases hb : b = c
  · subst b
    simp [m, mass, pointMass]
  · simp [m, mass, pointMass, hb]

theorem m_difference (i j : Index) (b : ℕ) :
    m (difference i j) b =
      (if b = i.1 then 1 else 0) - (if b = j.1 then 1 else 0) := by
  have hi := (absSummable_iff_summable _).mp (block_absSummable (pointMass_absSummable i) b)
  have hj := (absSummable_iff_summable _).mp (block_absSummable (pointMass_absSummable j) b)
  change (∑' n, (pointMass i (b, n) - pointMass j (b, n))) = _
  rw [hi.tsum_sub hj]
  exact congrArg₂ (· - ·) (m_pointMass i b) (m_pointMass j b)

/-- Every within-block difference has exactly zero block mass. -/
theorem m_sameBlock_difference (b j k : ℕ) : m (difference (b, j) (b, k)) = 0 := by
  funext c
  simp [m_difference]

/-- Frozen nonzero-block tests, with no restriction on j or k. -/
theorem nonzeroBlock_difference_mem_K (b : ℕ) (hb : b ≠ 0) (j k : ℕ) :
    difference (b, j) (b, k) ∈ K := by
  refine ⟨difference_absSummable _ _, m_sameBlock_difference _ _ _, ?_⟩
  simp only [r, difference, pointMass, Prod.mk.injEq]
  simp [Ne.symm hb]

/-- Frozen zero-block tail tests: source indices at least 3. -/
theorem zeroBlock_tail_difference_mem_K (j k : ℕ) (hj : 2 ≤ j) (hk : 2 ≤ k) :
    difference (0, j) (0, k) ∈ K := by
  refine ⟨difference_absSummable _ _, m_sameBlock_difference _ _ _, ?_⟩
  have hj0 : 0 ≠ j := by omega
  have hj1 : 1 ≠ j := by omega
  have hk0 : 0 ≠ k := by omega
  have hk1 : 1 ≠ k := by omega
  simp only [r, difference, pointMass, Prod.mk.injEq]
  simp [hj0, hj1, hk0, hk1]

/-- The exceptional head-head test. -/
theorem head_difference_mem_K : difference (0, 0) (0, 1) ∈ K := by
  refine ⟨difference_absSummable _ _, m_sameBlock_difference _ _ _, ?_⟩
  simp only [r, difference, pointMass, Prod.mk.injEq]
  norm_num

theorem annihilatesK_differenceTests {z : Index → ℝ} (hz : AnnihilatesK z) :
    BlockMassKernel.DifferenceTests z := by
  refine ⟨?_, ?_, ?_⟩
  · intro b hb j k
    apply sub_eq_zero.mp
    rw [← pairing_difference]
    exact hz _ (nonzeroBlock_difference_mem_K b hb j k)
  · intro j k hj hk
    apply sub_eq_zero.mp
    rw [← pairing_difference]
    exact hz _ (zeroBlock_tail_difference_mem_K j k hj hk)
  · apply sub_eq_zero.mp
    rw [← pairing_difference]
    exact hz _ head_difference_mem_K

/-- Both imported predicates concern the whole product index, not each row separately. -/
theorem globalC0_iff_kernel_globalC0 (z : Index → ℝ) :
    GlobalC0 z ↔ BlockMassKernel.GlobalC0 z :=
  globalC0_iff_tendsto z

/-- Genuine absolute convergence for every member of the full K. -/
theorem K_pairing_absSummable {z k : Index → ℝ} (hz : GlobalC0 z) (hk : k ∈ K) :
    AbsSummable (fun i => z i * k i) :=
  c0_pairing_absSummable hz hk.1

theorem annihilatesK_force_head_span {z : Index → ℝ}
    (hc0 : GlobalC0 z) (hz : AnnihilatesK z) :
    ∃ v : ℝ, ∀ i, z i = v * BlockMassKernel.headProfile i := by
  exact BlockMassKernel.difference_tests_force_head_span
    ((globalC0_iff_kernel_globalC0 z).mp hc0) (annihilatesK_differenceTests hz)

theorem headProfile_eq_pointMass (p : Index) :
    BlockMassKernel.headProfile p = -pointMass (0, 0) p - pointMass (0, 1) p := by
  by_cases h0 : p = (0, 0)
  · subst p
    simp only [BlockMassKernel.headProfile, pointMass, Prod.mk.injEq]
    norm_num
  · by_cases h1 : p = (0, 1)
    · subst p
      simp only [BlockMassKernel.headProfile, pointMass, Prod.mk.injEq]
      norm_num
    · simp only [BlockMassKernel.headProfile, pointMass, h0, h1, or_self, if_false,
        neg_zero, sub_self]

theorem headProfile_finite_support :
    (Function.support BlockMassKernel.headProfile).Finite := by
  apply ((Set.finite_singleton (0, 0)).union (Set.finite_singleton (0, 1))).subset
  intro p hp
  by_contra h
  have h0 : p ≠ (0, 0) := by intro h0; exact h (Or.inl h0)
  have h1 : p ≠ (0, 1) := by intro h1; exact h (Or.inr h1)
  exact hp (by simp only [BlockMassKernel.headProfile, h0, h1, or_self, if_false])

/-- The frozen signs give exactly r, not -r. No summability of k is needed here. -/
theorem pairing_headProfile (k : Index → ℝ) : pairing BlockMassKernel.headProfile k = r k := by
  have heq : (fun p => BlockMassKernel.headProfile p * k p) =
      (fun p => -(k p * pointMass (0, 0) p) - k p * pointMass (0, 1) p) := by
    funext p
    rw [headProfile_eq_pointMass]
    ring
  unfold pairing
  rw [heq, (pointMass_pairing_summable k (0, 0)).neg.tsum_sub
    (pointMass_pairing_summable k (0, 1)), tsum_neg]
  exact congrArg₂ (fun a b : ℝ => -a - b)
    (pairing_pointMass k (0, 0)) (pairing_pointMass k (0, 1))

theorem pairing_head_multiple (v : ℝ) (k : Index → ℝ) :
    pairing (fun i => v * BlockMassKernel.headProfile i) k = v * r k := by
  simp only [pairing, mul_assoc, tsum_mul_left]
  exact congrArg (v * ·) (pairing_headProfile k)

theorem head_multiple_globalC0 (v : ℝ) :
    GlobalC0 (fun i => v * BlockMassKernel.headProfile i) := by
  apply summable_globalC0
  exact (summable_of_finite_support headProfile_finite_support).mul_left v

theorem head_multiple_annihilatesK (v : ℝ) :
    AnnihilatesK (fun i => v * BlockMassKernel.headProfile i) := by
  intro k hk
  rw [pairing_head_multiple, hk.2.2, mul_zero]

/-- The annihilator in genuine global c0 is exactly the frozen head line. -/
theorem globalC0_annihilator_iff_head_span (z : Index → ℝ) :
    (GlobalC0 z ∧ AnnihilatesK z) ↔
      ∃ v : ℝ, ∀ i, z i = v * BlockMassKernel.headProfile i := by
  constructor
  · rintro ⟨hc0, hz⟩
    exact annihilatesK_force_head_span hc0 hz
  · rintro ⟨v, hv⟩
    have heq : z = fun i => v * BlockMassKernel.headProfile i := funext hv
    rw [heq]
    exact ⟨head_multiple_globalC0 v, head_multiple_annihilatesK v⟩

end BlockMassKernelTests
