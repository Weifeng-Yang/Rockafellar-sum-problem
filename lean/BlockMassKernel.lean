import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.Cofinite

/-!
C3 coordinate classification inside GLOBAL c0.
Lean (b,n) is source (b,n+1). This is the annihilator's topological
classification after finite difference tests have been obtained.
It does NOT assume that arbitrary continuous functionals have ell1 labels,
nor does it prove those tests from the actual graph's kernel in this file.
-/

noncomputable section
open Filter Topology

namespace BlockMassKernel

abbrev Index := ℕ × ℕ

def GlobalC0 (z : Index → ℝ) : Prop := Tendsto z cofinite (𝓝 0)

theorem globalC0_iff_finite_superlevels (z : Index → ℝ) :
    GlobalC0 z ↔ ∀ ε : ℝ, 0 < ε → Set.Finite {i | ε ≤ |z i|} := by
  simp only [GlobalC0, Metric.tendsto_nhds, Real.dist_eq, sub_zero,
    eventually_cofinite, not_lt]

/-- A nonzero constant cannot persist along any injective infinite slice. -/
theorem constant_injective_slice_eq_zero {z : Index → ℝ} (hz : GlobalC0 z)
    (φ : ℕ → Index) (hφ : Function.Injective φ) (c : ℝ)
    (hc : ∀ n, z (φ n) = c) : c = 0 := by
  have hcomp : z ∘ φ = fun _ => c := funext hc
  have ht : Tendsto (fun _ : ℕ => c) cofinite (𝓝 0) := by
    simpa only [hcomp] using hz.comp hφ.tendsto_cofinite
  exact tendsto_nhds_unique tendsto_const_nhds ht

/-- Equalities supplied by the actual finite difference tests in C3. -/
def DifferenceTests (z : Index → ℝ) : Prop :=
  (∀ b : ℕ, b ≠ 0 → ∀ j k : ℕ, z (b,j) = z (b,k)) ∧
  (∀ j k : ℕ, 2 ≤ j → 2 ≤ k → z (0,j) = z (0,k)) ∧
  z (0,0) = z (0,1)

def headProfile (i : Index) : ℝ :=
  if i = (0,0) ∨ i = (0,1) then -1 else 0

theorem nonzero_block_vanishes {z : Index → ℝ} (hz : GlobalC0 z)
    (ht : DifferenceTests z) (b : ℕ) (hb : b ≠ 0) (j : ℕ) : z (b,j) = 0 := by
  apply constant_injective_slice_eq_zero hz (fun n => (b,n))
    (fun _ _ h => congrArg Prod.snd h) (z (b,j))
  intro n
  exact ht.1 b hb n j

theorem zero_block_tail_vanishes {z : Index → ℝ} (hz : GlobalC0 z)
    (ht : DifferenceTests z) (j : ℕ) (hj : 2 ≤ j) : z (0,j) = 0 := by
  apply constant_injective_slice_eq_zero hz (fun n => (0,n+2))
    (fun _ _ h => Nat.add_right_cancel (congrArg Prod.snd h)) (z (0,j))
  intro n
  exact ht.2.1 (n+2) j (Nat.le_add_left 2 n) hj

/-- No blockwise-c0 substitute: the hypothesis is global cofinite convergence. -/
theorem difference_tests_force_head_span {z : Index → ℝ} (hz : GlobalC0 z)
    (ht : DifferenceTests z) : ∃ v : ℝ, ∀ i, z i = v * headProfile i := by
  refine ⟨-z (0,0), ?_⟩
  rintro ⟨b,j⟩
  by_cases hb : b = 0
  · subst b
    rcases j with _ | j
    · simp [headProfile]
    · rcases j with _ | j
      · simpa [headProfile] using ht.2.2.symm
      · have hj : 2 ≤ j + 1 + 1 := by omega
        simpa [headProfile] using zero_block_tail_vanishes hz ht (j+1+1) hj
  · simpa [headProfile, hb] using nonzero_block_vanishes hz ht b hb j

end BlockMassKernel

#print axioms BlockMassKernel.globalC0_iff_finite_superlevels
#print axioms BlockMassKernel.constant_injective_slice_eq_zero
#print axioms BlockMassKernel.nonzero_block_vanishes
#print axioms BlockMassKernel.zero_block_tail_vanishes
#print axioms BlockMassKernel.difference_tests_force_head_span
