import BlockMassFinite
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Instances.Real.Lemmas

/-!
Endpoint layer for certificate_r1/C0_CORE_PROOF_FROZEN.md,
section C4, equations C7-C8. Natural index n represents certificate n+1.

This file uses mathlib's actual Summable/HasSum and real topology. It does
not define c0, its full dual, E, m, L, the graph A, or its monotone polar.
The actual-row interface below takes finite-coordinate row inequalities;
deriving those from the full-dual polar and infinite squared norm is a
separate obligation. No endpoint is taken as an actual graph row.
-/

open scoped BigOperators Topology
open Filter

namespace BlockMassEndpoint

/-- The comparison coordinate 1/(4n), with positive indices shifted to Nat. -/
noncomputable def harmonicQuarter (n : ℕ) : ℝ := 1 / (4 * ((n : ℝ) + 1))

theorem harmonicQuarter_pos (n : ℕ) : 0 < harmonicQuarter n := by
  unfold harmonicQuarter
  positivity

/-- Finite-block lower bound, proved directly so no p-series import is needed. -/
theorem harmonicQuarter_block_lower (n : ℕ) (hn : 0 < n) :
    (1 : ℝ) / 8 ≤ ∑ k ∈ Finset.range n, harmonicQuarter (n + k) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    (1 : ℝ) / 8 = ∑ _k ∈ Finset.range n, (1 : ℝ) / (8 * (n : ℝ)) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [ne_of_gt hnR]
    _ ≤ ∑ k ∈ Finset.range n, harmonicQuarter (n + k) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkR : (k : ℝ) + 1 ≤ n := by
        exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hk)
      unfold harmonicQuarter
      apply one_div_le_one_div_of_le
      · positivity
      · push_cast
        linarith

/-- The shifted quarter harmonic sequence is not actually Summable in R.
The proof compares partial sums at n and 2n and takes their real limits. -/
theorem not_summable_harmonicQuarter : ¬ Summable harmonicQuarter := by
  intro hs
  have hlim := hs.hasSum.tendsto_sum_nat
  have hi : Tendsto (fun n : ℕ => n + 1) atTop atTop := tendsto_add_atTop_nat 1
  have hii : Tendsto (fun n : ℕ => (n + 1) + (n + 1)) atTop atTop := by
    apply tendsto_atTop_mono (fun n => Nat.le_add_right (n + 1) (n + 1)) hi
  have hdiff := (hlim.comp hii).sub (hlim.comp hi)
  have hbound (n : ℕ) : (1 : ℝ) / 8 ≤
      (∑ k ∈ Finset.range ((n + 1) + (n + 1)), harmonicQuarter k) -
      (∑ k ∈ Finset.range (n + 1), harmonicQuarter k) := by
    rw [Finset.sum_range_add]
    simpa only [add_sub_cancel_left] using
      harmonicQuarter_block_lower (n + 1) (Nat.zero_lt_succ n)
  have hzero : (1 : ℝ) / 8 ≤ 0 := by
    simpa only [sub_self] using ge_of_tendsto' hdiff hbound
  norm_num at hzero

/-- C7 for every finite N forces every coordinate, and also b=tau, nu=0.
The comparison vector w is arbitrary; no summability premise occurs here. -/
theorem coordinates_eq_of_all_endpoint_bounds (z w : ℕ → ℝ) (b tau nu : ℝ)
    (hlo : -1 ≤ tau) (hhi : tau ≤ 1)
    (hplus : ∀ N : ℕ, (b - 1) ^ 2 + nu ^ 2 +
      (∑ n ∈ Finset.range N, (z n - w n) ^ 2) ≤ (1 - tau) ^ 2)
    (hminus : ∀ N : ℕ, (b + 1) ^ 2 + nu ^ 2 +
      (∑ n ∈ Finset.range N, (z n - w n) ^ 2) ≤ (1 + tau) ^ 2) :
    b = tau ∧ nu = 0 ∧ z = w := by
  have hc (N : ℕ) := BlockMassFinite.c8_finite_endpoint_cancellation
    (Finset.range N) z w b tau nu hlo hhi (hplus N) (hminus N)
  have hc0 := hc 0
  simp only [Finset.range_zero, Finset.sum_empty, add_zero] at hc0
  have hb : (b - tau) ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg nu]) (sq_nonneg _)
  have hv : nu ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg (b - tau)]) (sq_nonneg _)
  refine ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp hb), sq_eq_zero_iff.mp hv, funext fun n => ?_⟩
  have hterm : (z n - w n) ^ 2 ≤
      ∑ i ∈ Finset.range (n + 1), (z i - w i) ^ 2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg (z i - w i))
      (Finset.mem_range.mpr (Nat.lt_succ_self n))
  have hz : (z n - w n) ^ 2 = 0 :=
    le_antisymm (by nlinarith [hc (n + 1), sq_nonneg (b - tau), sq_nonneg nu]) (sq_nonneg _)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)

/-- C7 excludes a real Summable tail on the entire closed interval [-1,1]. -/
theorem no_summable_endpoint (z : ℕ → ℝ) (b tau nu : ℝ)
    (hz : Summable z) (hlo : -1 ≤ tau) (hhi : tau ≤ 1)
    (hplus : ∀ N : ℕ, (b - 1) ^ 2 + nu ^ 2 +
      (∑ n ∈ Finset.range N, (z n - harmonicQuarter n) ^ 2) ≤ (1 - tau) ^ 2)
    (hminus : ∀ N : ℕ, (b + 1) ^ 2 + nu ^ 2 +
      (∑ n ∈ Finset.range N, (z n - harmonicQuarter n) ^ 2) ≤ (1 + tau) ^ 2) :
    False := by
  have heq := (coordinates_eq_of_all_endpoint_bounds z harmonicQuarter b tau nu hlo hhi hplus hminus).2.2
  exact not_summable_harmonicQuarter (heq ▸ hz)

/-- Literal C7 indexing: only positive truncation lengths are assumed.
The N=0 bound used by the general interface follows by discarding a square. -/
theorem no_summable_endpoint_positiveN (z : ℕ → ℝ) (b tau nu : ℝ)
    (hz : Summable z) (hlo : -1 ≤ tau) (hhi : tau ≤ 1)
    (hplus : ∀ N : ℕ, 0 < N → (b - 1) ^ 2 + nu ^ 2 +
      (∑ n ∈ Finset.range N, (z n - harmonicQuarter n) ^ 2) ≤ (1 - tau) ^ 2)
    (hminus : ∀ N : ℕ, 0 < N → (b + 1) ^ 2 + nu ^ 2 +
      (∑ n ∈ Finset.range N, (z n - harmonicQuarter n) ^ 2) ≤ (1 + tau) ^ 2) :
    False := by
  apply no_summable_endpoint z b tau nu hz hlo hhi
  · intro N
    have h := hplus (N + 1) (Nat.zero_lt_succ N)
    rw [Finset.sum_range_succ] at h
    nlinarith [sq_nonneg (z N - harmonicQuarter N)]
  · intro N
    have h := hminus (N + 1) (Nat.zero_lt_succ N)
    rw [Finset.sum_range_succ] at h
    nlinarith [sq_nonneg (z N - harmonicQuarter N)]

/-- The same exclusion with an explicit ell1-style absolute-summability premise. -/
theorem no_absolutely_summable_endpoint (z : ℕ → ℝ) (b tau nu : ℝ)
    (hz : Summable (fun n => |z n|)) (hlo : -1 ≤ tau) (hhi : tau ≤ 1)
    (hplus : ∀ N : ℕ, (b - 1) ^ 2 + nu ^ 2 +
      (∑ n ∈ Finset.range N, (z n - harmonicQuarter n) ^ 2) ≤ (1 - tau) ^ 2)
    (hminus : ∀ N : ℕ, (b + 1) ^ 2 + nu ^ 2 +
      (∑ n ∈ Finset.range N, (z n - harmonicQuarter n) ^ 2) ≤ (1 + tau) ^ 2) :
    False := by
  have heq := (coordinates_eq_of_all_endpoint_bounds z harmonicQuarter b tau nu hlo hhi hplus hminus).2.2
  have habs : (fun n => |harmonicQuarter n|) = harmonicQuarter :=
    funext (fun n => abs_of_pos (harmonicQuarter_pos n))
  exact not_summable_harmonicQuarter (by simpa only [heq, habs] using hz)

/-- Remove block zero from a genuinely Summable block-mass sequence. -/
theorem summable_tail (m : ℕ → ℝ) (hm : Summable m) :
    Summable (fun n => m (n + 1)) :=
  hm.comp_injective (fun _ _ h => Nat.add_right_cancel h)

/-- Transfer finite actual-row inequalities through coordinatewise limits.
Only s>0 is tested, corresponding to actual parameters 1+s and -1-s. -/
theorem endpoint_bounds_of_actual_rows
    (omega : ℝ → ℕ → ℝ) (z w : ℕ → ℝ) (b tau nu : ℝ)
    (homega : ∀ n, Tendsto (fun s => omega s n) (𝓝[>] (0 : ℝ)) (𝓝 (w n)))
    (hplus : ∀ s : ℝ, 0 < s → ∀ N : ℕ, (b - 1) ^ 2 + nu ^ 2 +
      (∑ n ∈ Finset.range N, (z n - omega s n) ^ 2) ≤ (1 + s - tau) ^ 2)
    (hminus : ∀ s : ℝ, 0 < s → ∀ N : ℕ, (b + 1) ^ 2 + nu ^ 2 +
      (∑ n ∈ Finset.range N, (z n - omega s n) ^ 2) ≤ (1 + s + tau) ^ 2) :
    (∀ N : ℕ, (b - 1) ^ 2 + nu ^ 2 +
      (∑ n ∈ Finset.range N, (z n - w n) ^ 2) ≤ (1 - tau) ^ 2) ∧
    (∀ N : ℕ, (b + 1) ^ 2 + nu ^ 2 +
      (∑ n ∈ Finset.range N, (z n - w n) ^ 2) ≤ (1 + tau) ^ 2) := by
  have hid : Tendsto (fun s : ℝ => s) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
  have hsums (N : ℕ) : Tendsto
      (fun s => ∑ n ∈ Finset.range N, (z n - omega s n) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (∑ n ∈ Finset.range N, (z n - w n) ^ 2)) := by
    apply tendsto_finset_sum
    intro n _
    exact (tendsto_const_nhds.sub (homega n)).pow 2
  constructor
  · intro N
    have h := le_of_tendsto_of_tendsto
      ((tendsto_const_nhds (x := (b - 1) ^ 2 + nu ^ 2)).add (hsums N))
      ((((tendsto_const_nhds (x := (1 : ℝ))).add hid).sub
        (tendsto_const_nhds (x := tau))).pow 2)
      (hpos.mono fun s hs => hplus s hs N)
    simpa only [add_zero] using h
  · intro N
    have h := le_of_tendsto_of_tendsto
      ((tendsto_const_nhds (x := (b + 1) ^ 2 + nu ^ 2)).add (hsums N))
      ((((tendsto_const_nhds (x := (1 : ℝ))).add hid).add
        (tendsto_const_nhds (x := tau))).pow 2)
      (hpos.mono fun s hs => hminus s hs N)
    simpa only [add_zero] using h

/-- The actual cutoff formula with a free fixed coefficient c_n.
For the frozen curve instantiate c_n=(n+1)^(1/4). No condition on c is
needed for the coordinatewise endpoint limit. -/
noncomputable def cutoff (c : ℕ → ℝ) (s : ℝ) (n : ℕ) : ℝ :=
  max (1 - s * c n) 0 / (4 * ((n : ℝ) + 1))

theorem cutoff_tendsto (c : ℕ → ℝ) (n : ℕ) :
    Tendsto (fun s => cutoff c s n) (𝓝[>] (0 : ℝ)) (𝓝 (harmonicQuarter n)) := by
  have hid : Tendsto (fun s : ℝ => s) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have h := (((tendsto_const_nhds (x := (1 : ℝ))).sub (hid.mul_const (c n))).max
    (tendsto_const_nhds (x := (0 : ℝ))))
  have hdiv := h.div_const
    (4 * ((n : ℝ) + 1))
  simpa only [cutoff, harmonicQuarter, zero_mul, sub_zero, max_eq_left (by norm_num : (0 : ℝ) ≤ 1)] using hdiv

/-- End-to-end endpoint exclusion from actual positive-s row inequalities.
Finite-N bounds and a true Summable sequence are inputs; the endpoint
bounds, zero residuals and harmonic contradiction are all proved. -/
theorem no_summable_actual_cutoff_rows (c z : ℕ → ℝ) (b tau nu : ℝ)
    (hz : Summable z) (hlo : -1 ≤ tau) (hhi : tau ≤ 1)
    (hplus : ∀ s : ℝ, 0 < s → ∀ N : ℕ, (b - 1) ^ 2 + nu ^ 2 +
      (∑ n ∈ Finset.range N, (z n - cutoff c s n) ^ 2) ≤ (1 + s - tau) ^ 2)
    (hminus : ∀ s : ℝ, 0 < s → ∀ N : ℕ, (b + 1) ^ 2 + nu ^ 2 +
      (∑ n ∈ Finset.range N, (z n - cutoff c s n) ^ 2) ≤ (1 + s + tau) ^ 2) :
    False := by
  obtain ⟨hp, hm⟩ := endpoint_bounds_of_actual_rows (cutoff c) z harmonicQuarter b tau nu
    (cutoff_tendsto c) hplus hminus
  exact no_summable_endpoint z b tau nu hz hlo hhi hp hm

/-- Discard the nonnegative tail of an actual convergent squared-distance
series. The convergence premise prevents misuse of the default value of tsum. -/
theorem finite_sq_bound_of_tsum (u : ℕ → ℝ) (a R : ℝ)
    (hu : Summable (fun n => (u n) ^ 2))
    (hbound : a + (∑' n, (u n) ^ 2) ≤ R) (N : ℕ) :
    a + (∑ n ∈ Finset.range N, (u n) ^ 2) ≤ R := by
  exact (add_le_add_left (hu.sum_le_tsum (Finset.range N) (fun n _ => sq_nonneg (u n))) a).trans hbound

/-- Equation C6 to endpoint exclusion with an actual infinite block-mass
sequence. m(0) is the head b; m(n+1) is the positive-block tail z_n.
Squared-distance summability is explicit; no infinite sum is treated as
a convergent sum without a proof. The coefficient c is arbitrary. -/
theorem no_summable_mass_cutoff_tsum_rows (c m : ℕ → ℝ) (tau nu : ℝ)
    (hm : Summable m) (hlo : -1 ≤ tau) (hhi : tau ≤ 1)
    (herr : ∀ s : ℝ, 0 < s → Summable (fun n => (m (n + 1) - cutoff c s n) ^ 2))
    (hplus : ∀ s : ℝ, 0 < s → (m 0 - 1) ^ 2 + nu ^ 2 +
      (∑' n, (m (n + 1) - cutoff c s n) ^ 2) ≤ (1 + s - tau) ^ 2)
    (hminus : ∀ s : ℝ, 0 < s → (m 0 + 1) ^ 2 + nu ^ 2 +
      (∑' n, (m (n + 1) - cutoff c s n) ^ 2) ≤ (1 + s + tau) ^ 2) :
    False := by
  apply no_summable_actual_cutoff_rows c (fun n => m (n + 1)) (m 0) tau nu
    (summable_tail m hm) hlo hhi
  · intro s hs N
    exact finite_sq_bound_of_tsum _ _ _ (herr s hs) (hplus s hs) N
  · intro s hs N
    exact finite_sq_bound_of_tsum _ _ _ (herr s hs) (hminus s hs) N

/-- A usable return value: these actual-row inequalities force tau outside
the closed gap. This is a scalar-sequence consequence, not graph maximality. -/
theorem tau_outside_of_summable_mass_rows (c m : ℕ → ℝ) (tau nu : ℝ)
    (hm : Summable m)
    (herr : ∀ s : ℝ, 0 < s → Summable (fun n => (m (n + 1) - cutoff c s n) ^ 2))
    (hplus : ∀ s : ℝ, 0 < s → (m 0 - 1) ^ 2 + nu ^ 2 +
      (∑' n, (m (n + 1) - cutoff c s n) ^ 2) ≤ (1 + s - tau) ^ 2)
    (hminus : ∀ s : ℝ, 0 < s → (m 0 + 1) ^ 2 + nu ^ 2 +
      (∑' n, (m (n + 1) - cutoff c s n) ^ 2) ≤ (1 + s + tau) ^ 2) :
    tau < -1 ∨ 1 < tau := by
  by_contra h
  push_neg at h
  exact no_summable_mass_cutoff_tsum_rows c m tau nu hm h.1 h.2 herr hplus hminus

end BlockMassEndpoint

#print axioms BlockMassEndpoint.harmonicQuarter_pos
#print axioms BlockMassEndpoint.harmonicQuarter_block_lower
#print axioms BlockMassEndpoint.not_summable_harmonicQuarter
#print axioms BlockMassEndpoint.coordinates_eq_of_all_endpoint_bounds
#print axioms BlockMassEndpoint.no_summable_endpoint
#print axioms BlockMassEndpoint.no_summable_endpoint_positiveN
#print axioms BlockMassEndpoint.no_absolutely_summable_endpoint
#print axioms BlockMassEndpoint.summable_tail
#print axioms BlockMassEndpoint.endpoint_bounds_of_actual_rows
#print axioms BlockMassEndpoint.cutoff_tendsto
#print axioms BlockMassEndpoint.no_summable_actual_cutoff_rows
#print axioms BlockMassEndpoint.finite_sq_bound_of_tsum
#print axioms BlockMassEndpoint.no_summable_mass_cutoff_tsum_rows
#print axioms BlockMassEndpoint.tau_outside_of_summable_mass_rows
