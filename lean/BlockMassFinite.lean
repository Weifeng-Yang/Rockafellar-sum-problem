import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!


Scope: real polynomial algebra for equation tags (C5) and (C8), not
sections C5/C8. The certificate has no section C8.

Frozen source: ../certificate/C0_CORE_PROOF_FROZEN.md
SHA256: 4FD199C655FB11C3B801699A6357D7AFCB862DBCB286C4E951AF02CF9847259A
Manifest: AE20120268B4D2E3382008C8FDAAC5B56181D176D7874B37381CAE7A7598E87A

No Banach space, dual identification, operator, infinite sum, limit,
maximality theorem, or Rockafellar conclusion is defined here. In C5 the
identification of the polynomial with the original dual pairing remains
an external obligation. In C8 the two endpoint inequalities are premises;
their derivation from actual graph rows remains an external obligation.

No theorem assumes its own conclusion. Axiom commands at the end must
actually run before any transitive axiom inventory can be reported.
-/

open scoped BigOperators

namespace BlockMassFinite

/-- Scalar C5 after substituting x = -Ep + v h into C4.
Here mp2, cross, and ft2 stand for the three quadratic pairing scalars.
The identity is unconditional over the reals. -/
theorem c5_square_completion (t v rp mp2 cross ft2 : ℝ) :
    (-mp2 + v * rp) - v * t + 2 * cross - t * rp + t ^ 2 - ft2 =
      (t - (v + rp) / 2) ^ 2 - ((v - rp) / 2) ^ 2 -
        (ft2 - 2 * cross + mp2) := by
  ring

/-- A finite Euclidean distance expansion. No infinite summation is used. -/
theorem finite_sq_distance {ι : Type*} (s : Finset ι) (a b : ι → ℝ) :
    (∑ i ∈ s, (a i - b i) ^ 2) =
      (∑ i ∈ s, (a i) ^ 2) - 2 * (∑ i ∈ s, a i * b i) +
        (∑ i ∈ s, (b i) ^ 2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [ih]
      ring

/-- C5 with all three quadratic quantities instantiated as finite sums.
This does not identify any finite sum with an infinite dual pairing. -/
theorem c5_finite_square_completion {ι : Type*} (s : Finset ι)
    (ft mp : ι → ℝ) (t v rp : ℝ) :
    (-(∑ i ∈ s, (mp i) ^ 2) + v * rp) - v * t +
        2 * (∑ i ∈ s, ft i * mp i) - t * rp + t ^ 2 -
        (∑ i ∈ s, (ft i) ^ 2) =
      (t - (v + rp) / 2) ^ 2 - ((v - rp) / 2) ^ 2 -
        (∑ i ∈ s, (ft i - mp i) ^ 2) := by
  rw [finite_sq_distance]
  exact c5_square_completion t v rp
    (∑ i ∈ s, (mp i) ^ 2) (∑ i ∈ s, ft i * mp i)
    (∑ i ∈ s, (ft i) ^ 2)

/-- The exact C8 weighted residual identity, including tau = -1 and 1.
The scalar S may later be replaced by a finite sum of squares. -/
theorem c8_weighted_endpoint_identity (b tau nu S : ℝ) :
    (1 + tau) / 2 * ((b - 1) ^ 2 + nu ^ 2 + S - (1 - tau) ^ 2) +
        (1 - tau) / 2 * ((b + 1) ^ 2 + nu ^ 2 + S - (1 + tau) ^ 2) =
      (b - tau) ^ 2 + nu ^ 2 + S := by
  ring

/-- C7 implies C8 by nonnegative weights, without dividing by a weight.
The hypotheses are the interval restriction and the two distinct C7
endpoint bounds. The C8 conclusion is not a hypothesis. -/
theorem c8_of_endpoint_bounds (b tau nu S : ℝ)
    (htauLower : -1 ≤ tau) (htauUpper : tau ≤ 1)
    (hplus : (b - 1) ^ 2 + nu ^ 2 + S ≤ (1 - tau) ^ 2)
    (hminus : (b + 1) ^ 2 + nu ^ 2 + S ≤ (1 + tau) ^ 2) :
    (b - tau) ^ 2 + nu ^ 2 + S ≤ 0 := by
  have hwplus : 0 ≤ (1 + tau) / 2 := by linarith
  have hwminus : 0 ≤ (1 - tau) / 2 := by linarith
  have hp := mul_nonpos_of_nonneg_of_nonpos hwplus (sub_nonpos.mpr hplus)
  have hm := mul_nonpos_of_nonneg_of_nonpos hwminus (sub_nonpos.mpr hminus)
  rw [← c8_weighted_endpoint_identity b tau nu S]
  exact add_nonpos hp hm

/-- C8 for an arbitrary finite set of real coordinates. To match C7,
use coordinates n = 1,...,N and w n = 1 / (4 * n). No endpoint is
asserted to belong to the graph by this theorem. -/
theorem c8_finite_endpoint_cancellation {ι : Type*} (s : Finset ι)
    (z w : ι → ℝ) (b tau nu : ℝ)
    (htauLower : -1 ≤ tau) (htauUpper : tau ≤ 1)
    (hplus : (b - 1) ^ 2 + nu ^ 2 +
      (∑ i ∈ s, (z i - w i) ^ 2) ≤ (1 - tau) ^ 2)
    (hminus : (b + 1) ^ 2 + nu ^ 2 +
      (∑ i ∈ s, (z i - w i) ^ 2) ≤ (1 + tau) ^ 2) :
    (b - tau) ^ 2 + nu ^ 2 + (∑ i ∈ s, (z i - w i) ^ 2) ≤ 0 := by
  exact c8_of_endpoint_bounds b tau nu (∑ i ∈ s, (z i - w i) ^ 2)
    htauLower htauUpper hplus hminus

end BlockMassFinite

#print axioms BlockMassFinite.c5_square_completion
#print axioms BlockMassFinite.finite_sq_distance
#print axioms BlockMassFinite.c5_finite_square_completion
#print axioms BlockMassFinite.c8_weighted_endpoint_identity
#print axioms BlockMassFinite.c8_of_endpoint_bounds
#print axioms BlockMassFinite.c8_finite_endpoint_cancellation
