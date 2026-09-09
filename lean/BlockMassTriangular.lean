import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
certificate_r1, D4 and C1 only.

Index dictionary: Lean (b,n) : Nat x Nat means source (b,n+1) in N0 x N.
The block index is unchanged. Source e_(0,1), e_(0,2), e_(0,3) therefore
have Lean coordinates (0,0), (0,1), (0,2). No source symbol is redefined.

`Ell1` is the actual space of absolutely summable real functions, with the
usual sum of absolute values. Mathlib `Summable` is unconditional summation
over all finite subsets, not conditional convergence along an enumeration.
`GlobalC0` is precisely the global finite-superlevel-set definition of c0.
It is not a condition imposed separately on each block.
-/

noncomputable section
open Filter Topology
open scoped BigOperators

namespace BlockMassTriangular

def AbsSummable {ι : Type*} (a : ι → ℝ) : Prop := Summable (fun i => |a i|)

abbrev Ell1 (ι : Type*) := {a : ι → ℝ // AbsSummable a}

def l1Size {ι : Type*} (a : ι → ℝ) : ℝ := ∑' i, |a i|

def GlobalC0 {ι : Type*} (x : ι → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Set.Finite {i | ε ≤ |x i|}

abbrev C0 (ι : Type*) := {x : ι → ℝ // GlobalC0 x}

theorem absSummable_iff_summable {ι : Type*} (a : ι → ℝ) :
    AbsSummable a ↔ Summable a := summable_abs_iff

theorem absSummable_iff_summable_norm {ι : Type*} (a : ι → ℝ) :
    AbsSummable a ↔ Summable (fun i => ‖a i‖) := by
  simp only [AbsSummable, Real.norm_eq_abs]

theorem globalC0_iff_tendsto {ι : Type*} (x : ι → ℝ) :
    GlobalC0 x ↔ Tendsto x cofinite (𝓝 0) := by
  simp only [GlobalC0, Metric.tendsto_nhds, Real.dist_eq, sub_zero,
    eventually_cofinite, not_lt]

theorem summable_globalC0 {ι : Type*} {a : ι → ℝ} (ha : Summable a) :
    GlobalC0 a := (globalC0_iff_tendsto a).2 ha.tendsto_cofinite_zero

def tail (a : ℕ → ℝ) (j : ℕ) : ℝ := ∑' k, if j < k then a k else 0

def E (a : ℕ → ℝ) (j : ℕ) : ℝ := a j + 2 * tail a j

def mass (a : ℕ → ℝ) : ℝ := ∑' j, a j

def pairing {ι : Type*} (x a : ι → ℝ) : ℝ := ∑' i, x i * a i

theorem tail_summable {a : ℕ → ℝ} (ha : AbsSummable a) (j : ℕ) :
    Summable (fun k => if j < k then a k else 0) := by
  apply Summable.of_norm_bounded (fun k => |a k|) ha
  intro k
  split_ifs <;> simp [Real.norm_eq_abs]

theorem tail_eq_shift (a : ℕ → ℝ) (j : ℕ) :
    tail a j = ∑' k, a (k + (j + 1)) := by
  have hinj : Function.Injective (fun k : ℕ => k + (j + 1)) :=
    fun _ _ h => Nat.add_right_cancel h
  have hsupport : Function.support (fun k => if j < k then a k else 0) ⊆
      Set.range (fun k : ℕ => k + (j + 1)) := by
    intro k hk
    have hjk : j < k := by
      by_contra h
      simp [Function.mem_support, h] at hk
    exact ⟨k - (j + 1), Nat.sub_add_cancel (by omega)⟩
  have h := hinj.tsum_eq hsupport
  have hlt (k : ℕ) : j < k + (j + 1) := by omega
  simpa only [tail, if_pos (hlt _)] using h.symm

theorem tail_tendsto_zero {a : ℕ → ℝ} (ha : AbsSummable a) :
    Tendsto (tail a) atTop (𝓝 0) := by
  have ha' : Summable a := (absSummable_iff_summable a).1 ha
  have hn : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right n 1) tendsto_id
  have hconst : Tendsto (fun _ : ℕ => ∑' k, a k) atTop (𝓝 (∑' k, a k)) :=
    tendsto_const_nhds
  have h := hconst.sub (ha'.hasSum.tendsto_sum_nat.comp hn)
  have heq : (fun n => (∑' k, a k) - ∑ k ∈ Finset.range (n + 1), a k) = tail a := by
    funext n
    rw [tail_eq_shift]
    linarith [ha'.sum_add_tsum_nat_add (n + 1)]
  simpa only [Function.comp_def, sub_self, heq] using h

theorem E_tendsto_zero {a : ℕ → ℝ} (ha : AbsSummable a) :
    Tendsto (E a) atTop (𝓝 0) := by
  have ha0 : Tendsto a atTop (𝓝 0) := by
    simpa only [Nat.cofinite_eq_atTop] using
      ((absSummable_iff_summable a).1 ha).tendsto_cofinite_zero
  simpa only [E, mul_zero, add_zero] using ha0.add
    (tendsto_const_nhds.mul (tail_tendsto_zero ha))

theorem E_globalC0 {a : ℕ → ℝ} (ha : AbsSummable a) : GlobalC0 (E a) := by
  apply (globalC0_iff_tendsto _).2
  simpa only [Nat.cofinite_eq_atTop] using E_tendsto_zero ha

def weight (j k : ℕ) : ℝ := if j = k then 1 else if j < k then 2 else 0

theorem weight_nonneg (j k : ℕ) : 0 ≤ weight j k := by
  unfold weight
  split_ifs <;> norm_num

theorem weight_le_two (j k : ℕ) : weight j k ≤ 2 := by
  unfold weight
  split_ifs <;> norm_num

theorem weight_symmetric (j k : ℕ) : weight j k + weight k j = 2 := by
  by_cases heq : j = k
  · subst k; norm_num [weight]
  · rcases lt_or_gt_of_ne heq with h | h
    · simp [weight, heq, Ne.symm heq, h, not_lt_of_ge h.le]
    · simp [weight, heq, Ne.symm heq, h, not_lt_of_ge h.le]

theorem weight_summable {a : ℕ → ℝ} (ha : AbsSummable a) (j : ℕ) :
    Summable (fun k => weight j k * a k) := by
  apply Summable.of_norm_bounded (fun k => 2 * |a k|) (ha.mul_left 2)
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (weight_nonneg j k)]
  exact mul_le_mul_of_nonneg_right (weight_le_two j k) (abs_nonneg _)

theorem E_eq_kernel {a : ℕ → ℝ} (ha : AbsSummable a) (j : ℕ) :
    E a j = ∑' k, weight j k * a k := by
  have hdiag : Summable (fun k => if k = j then a j else (0 : ℝ)) :=
    by
      apply Summable.of_norm_bounded (fun k => |a k|) ha
      intro k
      split_ifs with h
      · subst k; simp [Real.norm_eq_abs]
      · simp
  have heq : (fun k => weight j k * a k) =
      (fun k => (if k = j then a j else 0) + 2 * (if j < k then a k else 0)) := by
    funext k
    by_cases heq : j = k
    · subst k; simp [weight]
    · by_cases hlt : j < k <;> simp [weight, heq, Ne.symm heq, hlt]
  rw [heq, hdiag.tsum_add ((tail_summable ha j).mul_left 2), tsum_mul_left]
  simp [E, tail]

theorem E_abs_le {a : ℕ → ℝ} (ha : AbsSummable a) (j : ℕ) :
    |E a j| ≤ 2 * l1Size a := by
  have h := tsum_of_norm_bounded (ha.mul_left 2).hasSum (f := fun k => weight j k * a k)
    (fun k => show ‖weight j k * a k‖ ≤ 2 * |a k| by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (weight_nonneg j k)]
      exact mul_le_mul_of_nonneg_right (weight_le_two j k) (abs_nonneg _))
  simpa only [Real.norm_eq_abs, ← E_eq_kernel ha j, tsum_mul_left, l1Size] using h

theorem pairing_absSummable_of_bound {ι : Type*} {x a : ι → ℝ} {C : ℝ}
    (hx : ∀ i, |x i| ≤ C) (ha : AbsSummable a) :
    AbsSummable (fun i => x i * a i) := by
  apply Summable.of_nonneg_of_le (fun i => abs_nonneg _) _ (ha.mul_left C)
  intro i
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hx i) (abs_nonneg _)

theorem globalC0_bounded {ι : Type*} {x : ι → ℝ} (hx : GlobalC0 x) :
    ∃ C : ℝ, ∀ i, |x i| ≤ C := by
  have hf := (hx 1 zero_lt_one).image (fun i => |x i|)
  obtain ⟨C, hC⟩ := hf.bddAbove
  refine ⟨max C 1, fun i => ?_⟩
  by_cases hi : 1 ≤ |x i|
  · exact (hC ⟨i, hi, rfl⟩).trans (le_max_left _ _)
  · exact (le_of_lt (not_le.mp hi)).trans (le_max_right _ _)

theorem c0_pairing_absSummable {ι : Type*} {x a : ι → ℝ}
    (hx : GlobalC0 x) (ha : AbsSummable a) : AbsSummable (fun i => x i * a i) := by
  obtain ⟨C, hC⟩ := globalC0_bounded hx
  exact pairing_absSummable_of_bound hC ha

theorem E_pairing_absSummable {a c : ℕ → ℝ} (ha : AbsSummable a)
    (hc : AbsSummable c) : AbsSummable (fun j => E a j * c j) :=
  pairing_absSummable_of_bound (E_abs_le ha) hc

def kernelProduct (a c : ℕ → ℝ) (p : ℕ × ℕ) : ℝ :=
  weight p.1 p.2 * a p.2 * c p.1

theorem kernelProduct_absSummable {a c : ℕ → ℝ} (ha : AbsSummable a)
    (hc : AbsSummable c) : AbsSummable (kernelProduct a c) := by
  have hprod := hc.mul_of_nonneg ha (fun _ => abs_nonneg _) (fun _ => abs_nonneg _)
  apply Summable.of_nonneg_of_le (fun p => abs_nonneg _) _ (hprod.mul_left 2)
  intro p
  rw [kernelProduct, abs_mul, abs_mul, abs_of_nonneg (weight_nonneg _ _)]
  calc
    weight p.1 p.2 * |a p.2| * |c p.1| ≤ 2 * |a p.2| * |c p.1| :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (weight_le_two _ _) (abs_nonneg _)) (abs_nonneg _)
    _ = 2 * (|c p.1| * |a p.2|) := by ring

theorem pairing_E_eq_double {a c : ℕ → ℝ} (ha : AbsSummable a)
    (hc : AbsSummable c) : pairing (E a) c = ∑' p, kernelProduct a c p := by
  have hp := (absSummable_iff_summable _).1 (kernelProduct_absSummable ha hc)
  rw [hp.tsum_prod]
  unfold pairing
  apply tsum_congr
  intro j
  rw [E_eq_kernel ha j, ← tsum_mul_right]
  rfl

theorem E_symmetric_identity {a c : ℕ → ℝ} (ha : AbsSummable a)
    (hc : AbsSummable c) :
    pairing (E a) c + pairing (E c) a = 2 * mass a * mass c := by
  have hp := (absSummable_iff_summable _).1 (kernelProduct_absSummable ha hc)
  have hq := (absSummable_iff_summable _).1 (kernelProduct_absSummable hc ha)
  have hqs := hq.comp_injective (Equiv.prodComm ℕ ℕ).injective
  change Summable (fun p => kernelProduct c a ((Equiv.prodComm ℕ ℕ) p)) at hqs
  rw [pairing_E_eq_double ha hc, pairing_E_eq_double hc ha,
    ← (Equiv.prodComm ℕ ℕ).tsum_eq (kernelProduct c a), ← hp.tsum_add hqs]
  have heq : (fun p : ℕ × ℕ => kernelProduct a c p +
      kernelProduct c a ((Equiv.prodComm ℕ ℕ) p)) =
      (fun p : ℕ × ℕ => 2 * (c p.1 * a p.2)) := by
    funext p
    change weight p.1 p.2 * a p.2 * c p.1 +
      weight p.2 p.1 * c p.1 * a p.2 = 2 * (c p.1 * a p.2)
    calc
      _ = (weight p.1 p.2 + weight p.2 p.1) * (c p.1 * a p.2) := by ring
      _ = _ := by rw [weight_symmetric]
  rw [heq, tsum_mul_left]
  have hprod := tsum_mul_tsum_of_summable_norm
    ((absSummable_iff_summable_norm c).1 hc) ((absSummable_iff_summable_norm a).1 ha)
  rw [← hprod]
  unfold mass
  ring

theorem E_quadratic_identity {a : ℕ → ℝ} (ha : AbsSummable a) :
    pairing (E a) a = (mass a) ^ 2 := by
  nlinarith [E_symmetric_identity ha ha]

abbrev Index := ℕ × ℕ

def positiveIndexEquiv : ℕ ≃ {j : ℕ // 0 < j} where
  toFun n := ⟨n + 1, Nat.succ_pos n⟩
  invFun j := j.1 - 1
  left_inv n := by simp
  right_inv j := by
    apply Subtype.ext
    dsimp
    omega

def sourceIndexEquiv : Index ≃ ℕ × {j : ℕ // 0 < j} :=
  Equiv.prodCongr (Equiv.refl ℕ) positiveIndexEquiv

theorem sourceIndexEquiv_apply (b j : ℕ) :
    sourceIndexEquiv (b, j) = (b, ⟨j + 1, Nat.succ_pos j⟩) := rfl

def m (a : Index → ℝ) (b : ℕ) : ℝ := mass (fun j => a (b, j))

def blockSize (a : Index → ℝ) (b : ℕ) : ℝ := l1Size (fun j => a (b, j))

def blockE (a : Index → ℝ) (p : Index) : ℝ := E (fun j => a (p.1, j)) p.2

theorem block_absSummable {a : Index → ℝ} (ha : AbsSummable a) (b : ℕ) :
    AbsSummable (fun j => a (b, j)) := by
  exact ha.comp_injective (fun _ _ h => (Prod.mk.inj h).2)

theorem blockSize_summable {a : Index → ℝ} (ha : AbsSummable a) :
    Summable (blockSize a) := ha.prod

theorem blockSize_nonneg (a : Index → ℝ) (b : ℕ) : 0 ≤ blockSize a b :=
  tsum_nonneg (fun _ => abs_nonneg _)

theorem blockSize_total {a : Index → ℝ} (ha : AbsSummable a) :
    (∑' b, blockSize a b) = l1Size a := ha.tsum_prod.symm

theorem m_abs_le_blockSize {a : Index → ℝ} (ha : AbsSummable a) (b : ℕ) :
    |m a b| ≤ blockSize a b := by
  simpa only [m, mass, blockSize, l1Size, Real.norm_eq_abs] using
    norm_tsum_le_tsum_norm ((absSummable_iff_summable_norm _).1 (block_absSummable ha b))

theorem m_absSummable {a : Index → ℝ} (ha : AbsSummable a) : AbsSummable (m a) :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (m_abs_le_blockSize ha)
    (blockSize_summable ha)

theorem m_l1Size_le {a : Index → ℝ} (ha : AbsSummable a) : l1Size (m a) ≤ l1Size a := by
  rw [← blockSize_total ha]
  exact (m_absSummable ha).tsum_le_tsum (m_abs_le_blockSize ha) (blockSize_summable ha)

theorem blockE_abs_le_blockSize {a : Index → ℝ} (ha : AbsSummable a) (p : Index) :
    |blockE a p| ≤ 2 * blockSize a p.1 := E_abs_le (block_absSummable ha p.1) p.2

theorem blockE_abs_le {a : Index → ℝ} (ha : AbsSummable a) (p : Index) :
    |blockE a p| ≤ 2 * l1Size a := by
  apply (blockE_abs_le_blockSize ha p).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [← blockSize_total ha]
  exact (blockSize_summable ha).le_tsum p.1 (fun _ _ => blockSize_nonneg _ _)

theorem blockE_globalC0 {a : Index → ℝ} (ha : AbsSummable a) :
    GlobalC0 (blockE a) := by
  intro ε hε
  let B : Set ℕ := {b | ε / 2 ≤ blockSize a b}
  have hB : B.Finite := by
    have h := summable_globalC0 (blockSize_summable ha) (ε / 2) (by linarith)
    simpa only [abs_of_nonneg (blockSize_nonneg a _)] using h
  have hrow (b : ℕ) : Set.Finite {j | ε ≤ |blockE a (b, j)|} :=
    E_globalC0 (block_absSummable ha b) ε hε
  have hfinite : Set.Finite (⋃ b ∈ B, Prod.mk b '' {j | ε ≤ |blockE a (b, j)|}) :=
    hB.biUnion (fun b _ => (hrow b).image (Prod.mk b))
  apply hfinite.subset
  rintro ⟨b, j⟩ hp
  have hb : b ∈ B := by
    change ε / 2 ≤ blockSize a b
    have h := blockE_abs_le_blockSize ha (b, j)
    change ε ≤ |blockE a (b, j)| at hp
    dsimp only at h
    linarith
  exact Set.mem_iUnion.2 ⟨b, Set.mem_iUnion.2 ⟨hb, ⟨j, hp, rfl⟩⟩⟩

def EToC0 (a : Ell1 ℕ) : C0 ℕ := ⟨E a.1, E_globalC0 a.2⟩

def blockEToC0 (a : Ell1 Index) : C0 Index := ⟨blockE a.1, blockE_globalC0 a.2⟩

def mToEll1 (a : Ell1 Index) : Ell1 ℕ := ⟨m a.1, m_absSummable a.2⟩

theorem blockE_pairing_absSummable {a c : Index → ℝ} (ha : AbsSummable a)
    (hc : AbsSummable c) : AbsSummable (fun p => blockE a p * c p) :=
  pairing_absSummable_of_bound (blockE_abs_le ha) hc

theorem massProduct_absSummable {a c : Index → ℝ} (ha : AbsSummable a)
    (hc : AbsSummable c) : AbsSummable (fun b => m a b * m c b) := by
  apply pairing_absSummable_of_bound (C := l1Size (m a)) _ (m_absSummable hc)
  intro b
  exact (m_absSummable ha).le_tsum b (fun _ _ => abs_nonneg _)

theorem blockE_pairing_eq_iterated {a c : Index → ℝ} (ha : AbsSummable a)
    (hc : AbsSummable c) :
    pairing (blockE a) c = ∑' b, pairing (E (fun j => a (b, j))) (fun j => c (b, j)) :=
  ((absSummable_iff_summable _).1 (blockE_pairing_absSummable ha hc)).tsum_prod

/-- The actual infinite block C1, with absolutely convergent pairings on both sides. -/
theorem blockE_symmetric_identity {a c : Index → ℝ} (ha : AbsSummable a)
    (hc : AbsSummable c) :
    pairing (blockE a) c + pairing (blockE c) a = 2 * pairing (m a) (m c) := by
  have hp := ((absSummable_iff_summable _).1 (blockE_pairing_absSummable ha hc)).prod
  have hq := ((absSummable_iff_summable _).1 (blockE_pairing_absSummable hc ha)).prod
  change Summable (fun b => pairing (E (fun j => a (b, j))) (fun j => c (b, j))) at hp
  change Summable (fun b => pairing (E (fun j => c (b, j))) (fun j => a (b, j))) at hq
  rw [blockE_pairing_eq_iterated ha hc, blockE_pairing_eq_iterated hc ha,
    ← hp.tsum_add hq]
  calc
    _ = ∑' b, 2 * (m a b * m c b) := by
      apply tsum_congr
      intro b
      simpa only [m, mul_assoc] using
        E_symmetric_identity (block_absSummable ha b) (block_absSummable hc b)
    _ = 2 * pairing (m a) (m c) := tsum_mul_left

theorem m_square_summable {a : Index → ℝ} (ha : AbsSummable a) :
    Summable (fun b => (m a b) ^ 2) := by
  simpa only [pow_two] using
    (absSummable_iff_summable _).1 (massProduct_absSummable ha ha)

theorem blockE_quadratic_identity {a : Index → ℝ} (ha : AbsSummable a) :
    pairing (blockE a) a = ∑' b, (m a b) ^ 2 := by
  have h := blockE_symmetric_identity ha ha
  simp only [pairing, pow_two] at h ⊢
  linarith

theorem E_add {a c : ℕ → ℝ} (ha : AbsSummable a) (hc : AbsSummable c) :
    E (fun j => a j + c j) = fun j => E a j + E c j := by
  have hsum (j : ℕ) : tail (fun k => a k + c k) j = tail a j + tail c j := by
    unfold tail
    have heq : (fun k => if j < k then a k + c k else 0) =
        (fun k => (if j < k then a k else 0) + (if j < k then c k else 0)) := by
      funext k
      split_ifs <;> simp
    rw [heq, (tail_summable ha j).tsum_add (tail_summable hc j)]
  funext j
  simp only [E, hsum]
  ring

theorem E_smul (a : ℕ → ℝ) (r : ℝ) :
    E (fun j => r * a j) = fun j => r * E a j := by
  have hsum (j : ℕ) : tail (fun k => r * a k) j = r * tail a j := by
    unfold tail
    have heq : (fun k => if j < k then r * a k else 0) =
        (fun k => r * (if j < k then a k else 0)) := by
      funext k
      split_ifs <;> simp
    rw [heq, tsum_mul_left]
  funext j
  simp only [E, hsum]
  ring

theorem m_add {a c : Index → ℝ} (ha : AbsSummable a) (hc : AbsSummable c) :
    m (fun p => a p + c p) = fun b => m a b + m c b := by
  funext b
  exact ((absSummable_iff_summable _).1 (block_absSummable ha b)).tsum_add
    ((absSummable_iff_summable _).1 (block_absSummable hc b))

theorem m_smul (a : Index → ℝ) (r : ℝ) :
    m (fun p => r * a p) = fun b => r * m a b := by
  funext b
  exact tsum_mul_left

theorem blockE_add {a c : Index → ℝ} (ha : AbsSummable a) (hc : AbsSummable c) :
    blockE (fun p => a p + c p) = fun p => blockE a p + blockE c p := by
  funext p
  exact congrFun (E_add (block_absSummable ha p.1) (block_absSummable hc p.1)) p.2

theorem blockE_smul (a : Index → ℝ) (r : ℝ) :
    blockE (fun p => r * a p) = fun p => r * blockE a p := by
  funext p
  exact congrFun (E_smul (fun j => a (p.1, j)) r) p.2

end BlockMassTriangular
