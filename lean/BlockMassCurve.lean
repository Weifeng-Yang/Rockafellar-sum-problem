import BlockMassEndpoint
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Real.Sign

/-!
Actual frozen D6/D7 curve; positive certificate index j
is represented by n+1. This file does not define the Banach operators.
The endpoint layer is a sealed, read-only import.
-/

open scoped BigOperators Topology
open Filter

namespace BlockMassCurve

/-- Frozen coefficient (n+1)^(1/4), using the actual real power. -/
noncomputable def coeff (n : ℕ) : ℝ := Real.rpow ((n : ℝ) + 1) (1 / 4)

/-- Frozen omega_s, with shifted positive index. Only s>0 is actual. -/
noncomputable def omega (s : ℝ) (n : ℕ) : ℝ := BlockMassEndpoint.cutoff coeff s n

noncomputable def slope (n : ℕ) : ℝ := coeff n / (4 * ((n : ℝ) + 1))
noncomputable def weight (n : ℕ) : ℝ := (slope n) ^ 2
noncomputable def curveConstant : ℝ := ∑' n, weight n
noncomputable def W (s : ℝ) : ℝ := ∑' n, (omega s n) ^ 2

/-- Exact actual domain J; no endpoints. -/
def Actual (t : ℝ) : Prop := t < -1 ∨ 1 < t

/-- D7: head index zero and positive-block tail at index n+1. -/
noncomputable def wholeF (t : ℝ) : ℕ → ℝ
  | 0 => Real.sign t
  | n + 1 => omega (|t| - 1) n

theorem coeff_pos (n : ℕ) : 0 < coeff n :=
  Real.rpow_pos_of_pos (by positivity) _

theorem coeff_fourth (n : ℕ) : (coeff n) ^ 4 = (n : ℝ) + 1 := by
  unfold coeff
  rw [Real.rpow_eq_pow, ← Real.rpow_mul_natCast (by positivity)]
  norm_num

theorem omega_nonneg (s : ℝ) (n : ℕ) : 0 ≤ omega s n := by
  unfold omega BlockMassEndpoint.cutoff
  positivity

theorem omega_le_harmonic (s : ℝ) (hs : 0 ≤ s) (n : ℕ) :
    omega s n ≤ BlockMassEndpoint.harmonicQuarter n := by
  unfold omega BlockMassEndpoint.cutoff BlockMassEndpoint.harmonicQuarter
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact max_le (by nlinarith [mul_nonneg hs (coeff_pos n).le]) zero_le_one

/-- The real threshold is written (s^-1)^4, equal to the frozen s^(-4). -/
theorem omega_zero_of_threshold (s : ℝ) (hs : 0 < s) (n : ℕ)
    (hn : (s⁻¹) ^ 4 ≤ (n : ℝ) + 1) : omega s n = 0 := by
  have hr := Real.rpow_le_rpow (pow_nonneg (inv_nonneg.mpr hs.le) 4) hn
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hroot : ((s⁻¹) ^ 4) ^ (1 / 4 : ℝ) = s⁻¹ := by
    simpa only [one_div] using Real.pow_rpow_inv_natCast (inv_nonneg.mpr hs.le) (by norm_num : (4 : ℕ) ≠ 0)
  rw [hroot] at hr
  change s⁻¹ ≤ coeff n at hr
  have hmul := mul_le_mul_of_nonneg_left hr hs.le
  rw [mul_inv_cancel₀ hs.ne'] at hmul
  unfold omega BlockMassEndpoint.cutoff
  rw [max_eq_right (by linarith)]
  exact zero_div _

theorem omega_zero_above (s : ℝ) (hs : 0 < s) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → omega s n = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((s⁻¹) ^ 4)
  refine ⟨N, fun n hn => omega_zero_of_threshold s hs n ?_⟩
  have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem finite_support_of_zero_above (f : ℕ → ℝ)
    (h : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → f n = 0) : (Function.support f).Finite := by
  obtain ⟨N, hN⟩ := h
  apply (Finset.finite_toSet (Finset.range N)).subset
  intro n hn
  have hne : f n ≠ 0 := hn
  have hlt : n < N := by
    by_contra hge
    exact hne (hN n (Nat.le_of_not_gt hge))
  exact Finset.mem_range.mpr hlt

theorem omega_finite_support (s : ℝ) (hs : 0 < s) : (Function.support (omega s)).Finite :=
  finite_support_of_zero_above _ (omega_zero_above s hs)

theorem omega_summable (s : ℝ) (hs : 0 < s) : Summable (omega s) :=
  summable_of_finite_support (omega_finite_support s hs)

theorem omega_sq_summable (s : ℝ) (hs : 0 < s) : Summable (fun n => (omega s n) ^ 2) := by
  apply summable_of_finite_support
  apply (omega_finite_support s hs).subset
  intro n hn hz
  exact hn (by simp [hz])

theorem omega_sq_diff_summable (s q : ℝ) (hs : 0 < s) (hq : 0 < q) :
    Summable (fun n => (omega s n - omega q n) ^ 2) := by
  apply summable_of_finite_support
  apply ((omega_finite_support s hs).union (omega_finite_support q hq)).subset
  intro n hn
  simp only [Function.mem_support, Set.mem_union] at *
  by_contra h
  push_neg at h
  exact hn (by simp [h.1, h.2])

/-- General ell1-to-square-summability bridge, using absolute products and
the injective diagonal. No boundedness or summability conclusion is assumed. -/
theorem square_summable_of_summable (f : ℕ → ℝ) (hf : Summable f) :
    Summable (fun n => (f n) ^ 2) := by
  have ha := hf.abs
  have hp := ha.mul_of_nonneg ha (fun n => abs_nonneg (f n)) (fun n => abs_nonneg (f n))
  have hd := hp.comp_injective
    (fun _ _ h => congrArg Prod.fst h : Function.Injective (fun n : ℕ => (n, n)))
  simpa only [Function.comp_def, ← pow_two, sq_abs] using hd

/-- Discharges the sealed endpoint layer's square-error Summable premise
for every actual curve parameter and every real Summable mass tail. -/
theorem omega_error_sq_summable (m : ℕ → ℝ) (hm : Summable m) (s : ℝ) (hs : 0 < s) :
    Summable (fun n => (m n - omega s n) ^ 2) :=
  square_summable_of_summable _ (hm.sub (omega_summable s hs))

theorem omega_tendsto (n : ℕ) :
    Tendsto (fun s => omega s n) (𝓝[>] (0 : ℝ)) (𝓝 (BlockMassEndpoint.harmonicQuarter n)) :=
  BlockMassEndpoint.cutoff_tendsto coeff n

theorem slope_nonneg (n : ℕ) : 0 ≤ slope n := by
  unfold slope
  exact div_nonneg (coeff_pos n).le (by positivity)

/-- Pointwise C3 estimate, valid even before restricting to actual s,q. -/
theorem omega_coordinate_lipschitz (s q : ℝ) (n : ℕ) :
    |omega s n - omega q n| ≤ slope n * |s - q| := by
  unfold omega BlockMassEndpoint.cutoff slope
  rw [← sub_div, abs_div, abs_of_pos (by positivity : 0 < 4 * ((n : ℝ) + 1))]
  calc
    |max (1 - s * coeff n) 0 - max (1 - q * coeff n) 0| / (4 * ((n : ℝ) + 1))
      ≤ |(1 - s * coeff n) - (1 - q * coeff n)| / (4 * ((n : ℝ) + 1)) :=
        div_le_div_of_nonneg_right (abs_max_sub_max_le_abs _ _ _) (by positivity)
    _ = coeff n / (4 * ((n : ℝ) + 1)) * |s - q| := by
      rw [show (1 - s * coeff n) - (1 - q * coeff n) = (q - s) * coeff n by ring,
        abs_mul, abs_of_pos (coeff_pos n), abs_sub_comm q s]
      ring

theorem omega_coordinate_sq_bound (s q : ℝ) (n : ℕ) :
    (omega s n - omega q n) ^ 2 ≤ weight n * (s - q) ^ 2 := by
  have h := (sq_le_sq₀ (abs_nonneg (omega s n - omega q n))
    (mul_nonneg (slope_nonneg n) (abs_nonneg (s - q)))).mpr (omega_coordinate_lipschitz s q n)
  simpa only [mul_pow, sq_abs, weight] using h

/-- Exact frozen C3 coefficient, not a replacement curve or exponent. -/
theorem weight_eq_rpow (n : ℕ) :
    weight n = (1 / 16 : ℝ) * ((n : ℝ) + 1) ^ (-3 / 2 : ℝ) := by
  have hx : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  unfold weight slope coeff
  rw [Real.rpow_eq_pow, div_pow, ← Real.rpow_mul_natCast hx.le]
  norm_num [mul_pow]
  rw [show (-(3 / 2) : ℝ) = 1 / 2 - 2 by norm_num, Real.rpow_sub hx, Real.rpow_two]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem weight_summable : Summable weight := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-3 / 2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have ht := (hs.comp_injective (fun _ _ h => Nat.add_right_cancel h : Function.Injective (fun n : ℕ => n + 1))).mul_left (1 / 16 : ℝ)
  apply ht.congr
  intro n
  rw [weight_eq_rpow]
  simp only [Function.comp_def, Nat.cast_add, Nat.cast_one]

/-- A sufficient discrete numerical bound. This does not claim the sharp
integral comparison sum(n^-3/2)<3 from the frozen prose. -/
theorem rpow_sum_le_four : (∑' n : ℕ, (n : ℝ) ^ (-3 / 2 : ℝ)) ≤ 4 := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-3 / 2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hrpos : 0 ≤ (2 : ℝ) ^ (-1 / 2 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hrsq : ((2 : ℝ) ^ (-1 / 2 : ℝ)) ^ 2 = 1 / 2 := by
    rw [← Real.rpow_mul_natCast (by norm_num)]
    norm_num [Real.rpow_neg_one]
  have hrle : (2 : ℝ) ^ (-1 / 2 : ℝ) ≤ 3 / 4 := by nlinarith
  have hgeom (N : ℕ) :
      (∑ k ∈ Finset.range N, (3 / 4 : ℝ) ^ k) + 4 * (3 / 4 : ℝ) ^ N = 4 := by
    induction N with
    | zero => norm_num
    | succ N ih => rw [Finset.sum_range_succ, pow_succ]; nlinarith
  have hcondensed (k : ℕ) :
      (2 ^ k : ℕ) • (((2 ^ k : ℕ) : ℝ) ^ (-3 / 2 : ℝ)) =
      ((2 : ℝ) ^ (-1 / 2 : ℝ)) ^ k := by
    simp only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_two]
    calc
      (2 : ℝ) ^ k * ((2 : ℝ) ^ k) ^ (-3 / 2 : ℝ) =
          (2 : ℝ) ^ (k : ℝ) * (2 : ℝ) ^ ((k : ℝ) * (-3 / 2 : ℝ)) := by
            rw [Real.rpow_natCast, Real.rpow_natCast_mul (by norm_num)]
      _ = (2 : ℝ) ^ ((k : ℝ) + (k : ℝ) * (-3 / 2 : ℝ)) :=
        (Real.rpow_add (by norm_num) _ _).symm
      _ = ((2 : ℝ) ^ (-1 / 2 : ℝ)) ^ k := by
        rw [← Real.rpow_mul_natCast (by norm_num)]
        congr 1
        ring
  have hb (N : ℕ) : (∑ n ∈ Finset.range (2 ^ N), (n : ℝ) ^ (-3 / 2 : ℝ)) ≤ 4 := by
    have hc := Finset.le_sum_condensed
      (f := fun n : ℕ => (n : ℝ) ^ (-3 / 2 : ℝ))
      (fun m n hm hmn => Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hm)
        (by exact_mod_cast hmn) (by norm_num)) N
    simp only [Nat.cast_zero, Real.zero_rpow (by norm_num : (-3 / 2 : ℝ) ≠ 0), zero_add] at hc
    have hg : (∑ k ∈ Finset.range N, (2 ^ k : ℕ) • (((2 ^ k : ℕ) : ℝ) ^ (-3 / 2 : ℝ))) ≤
        ∑ k ∈ Finset.range N, (3 / 4 : ℝ) ^ k := by
      apply Finset.sum_le_sum
      intro k _
      rw [hcondensed]
      exact pow_le_pow_left₀ hrpos hrle k
    have hgn := pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) N
    linarith [hgeom N]
  exact le_of_tendsto' (hs.hasSum.tendsto_sum_nat.comp
    (Nat.tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ)))) hb

theorem curveConstant_eq :
    curveConstant = (1 / 16 : ℝ) * ∑' n : ℕ, ((n : ℝ) + 1) ^ (-3 / 2 : ℝ) := by
  unfold curveConstant
  simp_rw [weight_eq_rpow]
  rw [tsum_mul_left]

theorem curveConstant_nonneg : 0 ≤ curveConstant := tsum_nonneg (fun n => sq_nonneg (slope n))

theorem curveConstant_le_quarter : curveConstant ≤ 1 / 4 := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-3 / 2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have h := rpow_sum_le_four
  rw [hs.tsum_eq_zero_add] at h
  simp only [Nat.cast_zero, Real.zero_rpow (by norm_num : (-3 / 2 : ℝ) ≠ 0), zero_add,
    Nat.cast_add, Nat.cast_one] at h
  rw [curveConstant_eq]
  linarith

/-- The true infinite squared-distance C3 estimate, with its exact coefficient. -/
theorem omega_sq_lipschitz (s q : ℝ) (hs : 0 < s) (hq : 0 < q) :
    (∑' n, (omega s n - omega q n) ^ 2) ≤ curveConstant * (s - q) ^ 2 := by
  have h := (omega_sq_diff_summable s q hs hq).tsum_le_tsum
    (fun n => omega_coordinate_sq_bound s q n) (weight_summable.mul_right ((s - q) ^ 2))
  simpa only [tsum_mul_right, curveConstant] using h

theorem actual_gap_pos (t : ℝ) (ht : Actual t) : 0 < |t| - 1 := by
  rcases ht with ht | ht
  · rw [abs_of_neg (by linarith)]
    linarith
  · rw [abs_of_pos (by linarith)]
    linarith

theorem wholeF_finite_support (t : ℝ) (ht : Actual t) : (Function.support (wholeF t)).Finite := by
  obtain ⟨N, hN⟩ := omega_zero_above (|t| - 1) (actual_gap_pos t ht)
  apply finite_support_of_zero_above
  refine ⟨N + 1, fun n hn => ?_⟩
  cases n with
  | zero => exact (Nat.not_succ_le_zero N hn).elim
  | succ n => exact hN n (Nat.le_of_succ_le_succ hn)

theorem wholeF_summable (t : ℝ) (ht : Actual t) : Summable (wholeF t) :=
  summable_of_finite_support (wholeF_finite_support t ht)

theorem wholeF_sq_summable (t : ℝ) (ht : Actual t) : Summable (fun n => (wholeF t n) ^ 2) :=
  square_summable_of_summable _ (wholeF_summable t ht)

theorem wholeF_sq_diff_summable (t u : ℝ) (ht : Actual t) (hu : Actual u) :
    Summable (fun n => (wholeF t n - wholeF u n) ^ 2) := by
  apply summable_of_finite_support
  apply ((wholeF_finite_support t ht).union (wholeF_finite_support u hu)).subset
  intro n hn
  simp only [Function.mem_support, Set.mem_union] at *
  by_contra h
  push_neg at h
  exact hn (by simp [h.1, h.2])

/-- Scalar geometry of the two actual branches, including opposite signs. -/
theorem sign_abs_gap_bound (t u : ℝ) (ht : Actual t) (hu : Actual u) :
    (Real.sign t - Real.sign u) ^ 2 + (|t| - |u|) ^ 2 ≤ (t - u) ^ 2 := by
  rcases ht with ht | ht <;> rcases hu with hu | hu
  · rw [Real.sign_of_neg (by linarith), Real.sign_of_neg (by linarith),
      abs_of_neg (by linarith), abs_of_neg (by linarith)]
    nlinarith
  · rw [Real.sign_of_neg (by linarith), Real.sign_of_pos (by linarith),
      abs_of_neg (by linarith), abs_of_pos (by linarith)]
    nlinarith [mul_nonneg (by linarith : 0 ≤ -t - 1) (by linarith : 0 ≤ u - 1)]
  · rw [Real.sign_of_pos (by linarith), Real.sign_of_neg (by linarith),
      abs_of_pos (by linarith), abs_of_neg (by linarith)]
    nlinarith [mul_nonneg (by linarith : 0 ≤ t - 1) (by linarith : 0 ≤ -u - 1)]
  · rw [Real.sign_of_pos (by linarith), Real.sign_of_pos (by linarith),
      abs_of_pos (by linarith), abs_of_pos (by linarith)]
    nlinarith

/-- Whole-F 1-Lipschitz in the exact infinite squared-distance form needed
by the frozen C2 pairing identity to establish graph monotonicity. -/
theorem wholeF_sq_lipschitz (t u : ℝ) (ht : Actual t) (hu : Actual u) :
    (∑' n, (wholeF t n - wholeF u n) ^ 2) ≤ (t - u) ^ 2 := by
  have htail := omega_sq_lipschitz (|t| - 1) (|u| - 1) (actual_gap_pos t ht) (actual_gap_pos u hu)
  have hc : curveConstant ≤ 1 := le_trans curveConstant_le_quarter (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right hc (sq_nonneg ((|t| - 1) - (|u| - 1)))
  have hgeom := sign_abs_gap_bound t u ht hu
  rw [(wholeF_sq_diff_summable t u ht hu).tsum_eq_zero_add]
  change (Real.sign t - Real.sign u) ^ 2 +
    (∑' n, (omega (|t| - 1) n - omega (|u| - 1) n) ^ 2) ≤ (t - u) ^ 2
  nlinarith

/-- Usual scalar ell2-distance reading of the preceding squared estimate.
No custom metric or summability axiom is introduced. -/
theorem wholeF_lipschitz_distance (t u : ℝ) (ht : Actual t) (hu : Actual u) :
    Real.sqrt (∑' n, (wholeF t n - wholeF u n) ^ 2) ≤ |t - u| := by
  have h := Real.sqrt_le_sqrt (wholeF_sq_lipschitz t u ht hu)
  simpa only [Real.sqrt_sq_eq_abs] using h

end BlockMassCurve

#print axioms BlockMassCurve.coeff_pos
#print axioms BlockMassCurve.coeff_fourth
#print axioms BlockMassCurve.omega_nonneg
#print axioms BlockMassCurve.omega_le_harmonic
#print axioms BlockMassCurve.omega_zero_of_threshold
#print axioms BlockMassCurve.omega_zero_above
#print axioms BlockMassCurve.finite_support_of_zero_above
#print axioms BlockMassCurve.omega_finite_support
#print axioms BlockMassCurve.omega_summable
#print axioms BlockMassCurve.omega_sq_summable
#print axioms BlockMassCurve.omega_sq_diff_summable
#print axioms BlockMassCurve.square_summable_of_summable
#print axioms BlockMassCurve.omega_error_sq_summable
#print axioms BlockMassCurve.omega_tendsto
#print axioms BlockMassCurve.slope_nonneg
#print axioms BlockMassCurve.omega_coordinate_lipschitz
#print axioms BlockMassCurve.omega_coordinate_sq_bound
#print axioms BlockMassCurve.weight_eq_rpow
#print axioms BlockMassCurve.weight_summable
#print axioms BlockMassCurve.rpow_sum_le_four
#print axioms BlockMassCurve.curveConstant_eq
#print axioms BlockMassCurve.curveConstant_nonneg
#print axioms BlockMassCurve.curveConstant_le_quarter
#print axioms BlockMassCurve.omega_sq_lipschitz
#print axioms BlockMassCurve.actual_gap_pos
#print axioms BlockMassCurve.wholeF_finite_support
#print axioms BlockMassCurve.wholeF_summable
#print axioms BlockMassCurve.wholeF_sq_summable
#print axioms BlockMassCurve.wholeF_sq_diff_summable
#print axioms BlockMassCurve.sign_abs_gap_bound
#print axioms BlockMassCurve.wholeF_sq_lipschitz
#print axioms BlockMassCurve.wholeF_lipschitz_distance
