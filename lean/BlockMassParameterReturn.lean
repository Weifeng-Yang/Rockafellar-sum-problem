import BlockMassCurve

/-!
Exact scalar-sequence return interface after the all-polar
bracket has been derived. This does not assume or prove that arbitrary
Banach-space polar points satisfy that bracket; the graph interface remains
a separate obligation. All test parameters below are actual (strictly |t|>1).
-/

noncomputable section
open scoped BigOperators
open BlockMassCurve

namespace BlockMassParameterReturn

def ActualRowBounds (m : ℕ → ℝ) (tau nu : ℝ) : Prop :=
  ∀ t : ℝ, Actual t →
    nu ^ 2 + (∑' b, (m b - wholeF t b) ^ 2) ≤ (t - tau) ^ 2

theorem error_sq_summable (m : ℕ → ℝ) (hm : Summable m)
    (t : ℝ) (ht : Actual t) :
    Summable (fun b => (m b - wholeF t b) ^ 2) :=
  square_summable_of_summable _ (hm.sub (wholeF_summable t ht))

theorem positive_row_bound (m : ℕ → ℝ) (hm : Summable m) (tau nu : ℝ)
    (hr : ActualRowBounds m tau nu) (s : ℝ) (hs : 0 < s) :
    (m 0 - 1) ^ 2 + nu ^ 2 +
      (∑' n, (m (n+1) - omega s n) ^ 2) ≤ (1+s-tau) ^ 2 := by
  have ht : Actual (1+s) := Or.inr (by linarith)
  have h := hr (1+s) ht
  rw [(error_sq_summable m hm (1+s) ht).tsum_eq_zero_add] at h
  have hsign : Real.sign (1+s) = (1 : ℝ) := Real.sign_of_pos (by linarith)
  have habs : |1+s| - 1 = s := by rw [abs_of_pos (by linarith)]; ring
  simp only [wholeF, hsign, habs] at h
  linarith

theorem negative_row_bound (m : ℕ → ℝ) (hm : Summable m) (tau nu : ℝ)
    (hr : ActualRowBounds m tau nu) (s : ℝ) (hs : 0 < s) :
    (m 0 + 1) ^ 2 + nu ^ 2 +
      (∑' n, (m (n+1) - omega s n) ^ 2) ≤ (1+s+tau) ^ 2 := by
  have ht : Actual (-1-s) := Or.inl (by linarith)
  have h := hr (-1-s) ht
  rw [(error_sq_summable m hm (-1-s) ht).tsum_eq_zero_add] at h
  have hsign : Real.sign (-1-s) = (-1 : ℝ) := Real.sign_of_neg (by linarith)
  have habs : |-1-s| - 1 = s := by rw [abs_of_neg (by linarith)]; ring
  simp only [wholeF, hsign, habs, sub_neg_eq_add] at h
  nlinarith

theorem tau_actual (m : ℕ → ℝ) (hm : Summable m) (tau nu : ℝ)
    (hr : ActualRowBounds m tau nu) : Actual tau := by
  apply BlockMassEndpoint.tau_outside_of_summable_mass_rows coeff m tau nu hm
  · intro s hs
    exact omega_error_sq_summable (fun n => m (n+1))
      (BlockMassEndpoint.summable_tail m hm) s hs
  · exact positive_row_bound m hm tau nu hr
  · exact negative_row_bound m hm tau nu hr

theorem parameter_return (m : ℕ → ℝ) (hm : Summable m) (tau nu : ℝ)
    (hr : ActualRowBounds m tau nu) :
    Actual tau ∧ nu = 0 ∧ m = wholeF tau := by
  have ht := tau_actual m hm tau nu hr
  have h := hr tau ht
  have hsum : 0 ≤ ∑' b, (m b - wholeF tau b) ^ 2 :=
    tsum_nonneg (fun b => sq_nonneg _)
  have hnusq : nu ^ 2 = 0 := by nlinarith [sq_nonneg nu]
  refine ⟨ht, sq_eq_zero_iff.mp hnusq, ?_⟩
  funext b
  have hb := (error_sq_summable m hm tau ht).le_tsum b (fun n _ => sq_nonneg _)
  have hsq : (m b - wholeF tau b) ^ 2 = 0 := by nlinarith [sq_nonneg (m b - wholeF tau b)]
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)

theorem actual_parameters_satisfy_rows (tau : ℝ) (htau : Actual tau) :
    ActualRowBounds (wholeF tau) tau 0 := by
  intro t ht
  have h := wholeF_sq_lipschitz tau t htau ht
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add]
  nlinarith

/-- Exact parameter cell, not an assumed Banach-space polar theorem. -/
theorem actual_row_bounds_iff (m : ℕ → ℝ) (hm : Summable m) (tau nu : ℝ) :
    ActualRowBounds m tau nu ↔ Actual tau ∧ nu = 0 ∧ m = wholeF tau := by
  constructor
  · exact parameter_return m hm tau nu
  · rintro ⟨ht, rfl, rfl⟩
    exact actual_parameters_satisfy_rows tau ht

end BlockMassParameterReturn

#print axioms BlockMassParameterReturn.error_sq_summable
#print axioms BlockMassParameterReturn.positive_row_bound
#print axioms BlockMassParameterReturn.negative_row_bound
#print axioms BlockMassParameterReturn.tau_actual
#print axioms BlockMassParameterReturn.parameter_return
#print axioms BlockMassParameterReturn.actual_parameters_satisfy_rows
#print axioms BlockMassParameterReturn.actual_row_bounds_iff
