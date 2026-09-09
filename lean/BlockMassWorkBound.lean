import BlockMassCurve

/-!
certificate_r1 D6 / C11 numerical obligation only.
Source positive index j corresponds to Lean n+1, exactly as in the sealed
endpoint and actual-curve modules. Their harmonicQuarter, omega, W, and
Actual definitions are used unchanged. No Banach graph is defined here.

The reciprocal-square estimate is entirely discrete. The first two terms
are kept exactly; the tail is bounded by a telescoping sum. No Basel
identity, tail-limit assumption, sigma bound, or W bound is assumed.
-/

open scoped BigOperators Topology
open Filter

namespace BlockMassWorkBound

open BlockMassEndpoint BlockMassCurve

noncomputable def inverseSquare (n : ℕ) : ℝ := 1 / (((n : ℝ) + 1) ^ 2)

/-- The source sigma series, with the same shifted harmonic coordinate. -/
noncomputable def sigmaSeries : ℝ := ∑' n, (harmonicQuarter n) ^ 2

theorem inverseSquare_nonneg (n : ℕ) : 0 ≤ inverseSquare n := by
  unfold inverseSquare
  positivity

theorem reciprocal_square_step (x : ℝ) (hx : 0 < x) :
    1 / (x + 1) ^ 2 ≤ 1 / x - 1 / (x + 1) := by
  have hx1 : 0 < x + 1 := by linarith
  calc
    1 / (x + 1) ^ 2 ≤ 1 / (x * (x + 1)) :=
      one_div_le_one_div_of_le (mul_pos hx hx1) (by nlinarith)
    _ = 1 / x - 1 / (x + 1) := by
      field_simp

/-- Tail starts at source j=3. The source j=2 term remains exactly 1/4. -/
theorem inverseSquare_tail_step (n : ℕ) :
    inverseSquare (n + 2) ≤ 1 / ((n : ℝ) + 2) - 1 / (((n : ℝ) + 2) + 1) := by
  simpa only [inverseSquare, Nat.cast_add, Nat.cast_ofNat] using
    reciprocal_square_step ((n : ℝ) + 2) (by positivity)

theorem inverseSquare_tail_partial (N : ℕ) :
    (∑ n ∈ Finset.range N, inverseSquare (n + 2)) + 1 / ((N : ℝ) + 2) ≤ 1 / 2 := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ,
      show ((N : ℝ) + 1) + 2 = ((N : ℝ) + 2) + 1 by ring]
    linarith [inverseSquare_tail_step N]

theorem inverseSquare_partial_split (N : ℕ) :
    (∑ n ∈ Finset.range (N + 2), inverseSquare n) =
      5 / 4 + ∑ n ∈ Finset.range N, inverseSquare (n + 2) := by
  have htwo : (∑ n ∈ Finset.range 2, inverseSquare n) = (5 / 4 : ℝ) := by
    norm_num [Finset.sum_range_succ, inverseSquare]
  rw [Nat.add_comm N 2, Finset.sum_range_add, htwo]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  rw [Nat.add_comm]

theorem inverseSquare_partial_le_seven_fourths (N : ℕ) :
    (∑ n ∈ Finset.range N, inverseSquare n) ≤ 7 / 4 := by
  rcases N with _ | N
  · norm_num
  rcases N with _ | N
  · norm_num [Finset.sum_range_succ, inverseSquare]
  · rw [show N + 1 + 1 = N + 2 by omega, inverseSquare_partial_split]
    have hn : 0 ≤ 1 / ((N : ℝ) + 2) := by positivity
    linarith [inverseSquare_tail_partial N]

/-- Genuine convergence, obtained from the finite bounds and positivity. -/
theorem inverseSquare_summable : Summable inverseSquare :=
  summable_of_sum_range_le inverseSquare_nonneg inverseSquare_partial_le_seven_fourths

theorem inverseSquare_tsum_le_seven_fourths : (∑' n, inverseSquare n) ≤ 7 / 4 :=
  le_of_tendsto' inverseSquare_summable.hasSum.tendsto_sum_nat
    inverseSquare_partial_le_seven_fourths

theorem harmonicQuarter_sq_eq (n : ℕ) :
    (harmonicQuarter n) ^ 2 = (1 / 16 : ℝ) * inverseSquare n := by
  unfold harmonicQuarter inverseSquare
  simp only [div_pow, mul_pow, one_pow]
  norm_num
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem harmonicQuarter_sq_summable : Summable (fun n => (harmonicQuarter n) ^ 2) := by
  apply (inverseSquare_summable.mul_left (1 / 16 : ℝ)).congr
  intro n
  exact (harmonicQuarter_sq_eq n).symm

theorem harmonicQuarter_sq_hasSum : HasSum (fun n => (harmonicQuarter n) ^ 2) sigmaSeries :=
  harmonicQuarter_sq_summable.hasSum

theorem sigmaSeries_eq_scaled : sigmaSeries = (1 / 16 : ℝ) * ∑' n, inverseSquare n := by
  unfold sigmaSeries
  simp_rw [harmonicQuarter_sq_eq]
  rw [tsum_mul_left]

theorem sigmaSeries_nonneg : 0 ≤ sigmaSeries := tsum_nonneg (fun n => sq_nonneg (harmonicQuarter n))

theorem sigmaSeries_le_seven_sixtyfourths : sigmaSeries ≤ 7 / 64 := by
  rw [sigmaSeries_eq_scaled]
  linarith [inverseSquare_tsum_le_seven_fourths]

theorem sigmaSeries_lt_one_eighth : sigmaSeries < 1 / 8 :=
  lt_of_le_of_lt sigmaSeries_le_seven_sixtyfourths (by norm_num)

theorem omega_sq_le_harmonicQuarter_sq (s : ℝ) (hs : 0 < s) (n : ℕ) :
    (omega s n) ^ 2 ≤ (harmonicQuarter n) ^ 2 :=
  (sq_le_sq₀ (omega_nonneg s n) (harmonicQuarter_pos n).le).mpr
    (omega_le_harmonic s hs.le n)

theorem W_hasSum (s : ℝ) (hs : 0 < s) : HasSum (fun n => (omega s n) ^ 2) (W s) :=
  (omega_sq_summable s hs).hasSum

theorem W_nonneg (s : ℝ) (hs : 0 < s) : 0 ≤ W s :=
  (W_hasSum s hs).nonneg (fun n => sq_nonneg (omega s n))

theorem W_le_sigmaSeries (s : ℝ) (hs : 0 < s) : W s ≤ sigmaSeries :=
  (omega_sq_summable s hs).tsum_le_tsum (omega_sq_le_harmonicQuarter_sq s hs)
    harmonicQuarter_sq_summable

theorem W_bounds (s : ℝ) (hs : 0 < s) : 0 ≤ W s ∧ W s ≤ sigmaSeries :=
  ⟨W_nonneg s hs, W_le_sigmaSeries s hs⟩

theorem W_lt_one_eighth (s : ℝ) (hs : 0 < s) : W s < 1 / 8 :=
  lt_of_le_of_lt (W_le_sigmaSeries s hs) sigmaSeries_lt_one_eighth

theorem actual_square_gt_one (t : ℝ) (ht : Actual t) : 1 < t ^ 2 := by
  rcases ht with ht | ht
  · nlinarith [sq_nonneg (t + 1)]
  · nlinarith [sq_nonneg (t - 1)]

/-- No W-bound hypothesis: only membership in the actual parameter set J. -/
theorem actual_work_gt_one_sub_sigma (t : ℝ) (ht : Actual t) :
    1 - sigmaSeries < 2 * t ^ 2 - 1 - W (|t| - 1) := by
  have hw := W_le_sigmaSeries (|t| - 1) (actual_gap_pos t ht)
  linarith [actual_square_gt_one t ht]

theorem actual_work_gt_fiftyseven_sixtyfourths (t : ℝ) (ht : Actual t) :
    57 / 64 < 2 * t ^ 2 - 1 - W (|t| - 1) := by
  linarith [actual_work_gt_one_sub_sigma t ht, sigmaSeries_le_seven_sixtyfourths]

/-- The exact strict C11 numerical conclusion, for every actual t in J. -/
theorem sum_witness_work_bound (t : ℝ) (ht : Actual t) :
    7 / 8 < 2 * t ^ 2 - 1 - W (|t| - 1) :=
  lt_trans (by norm_num : (7 / 8 : ℝ) < 57 / 64)
    (actual_work_gt_fiftyseven_sixtyfourths t ht)

/-- Actual positive curve parameter, true series convergence, range bound,
and the strict work conclusion together. No graph or pairing is assumed. -/
theorem actual_work_certificate (t : ℝ) (ht : Actual t) :
    0 < |t| - 1 ∧ Summable (fun n => (omega (|t| - 1) n) ^ 2) ∧
      0 ≤ W (|t| - 1) ∧ W (|t| - 1) ≤ sigmaSeries ∧
      sigmaSeries < 1 / 8 ∧ 7 / 8 < 2 * t ^ 2 - 1 - W (|t| - 1) :=
  ⟨actual_gap_pos t ht, omega_sq_summable _ (actual_gap_pos t ht),
    W_nonneg _ (actual_gap_pos t ht), W_le_sigmaSeries _ (actual_gap_pos t ht),
    sigmaSeries_lt_one_eighth, sum_witness_work_bound t ht⟩

end BlockMassWorkBound
