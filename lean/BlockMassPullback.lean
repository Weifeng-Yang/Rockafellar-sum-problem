import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Full-continuous-dual pullback under a surjective Banach-space map

Independent r1 L2 transport lemma.
The definitions follow certificate_r1/DEFINITIONS_FROZEN.md (D1).
No BlockMass counterexample, other lane theorem, or finite algebra is imported.

In this pinned mathlib, `NormedSpace.Dual` is an abbreviation for `E →L[ℝ] ℝ`
in a larger module; we use that underlying type directly. This version has no
`ContinuousLinearMap.dualMap` API, so the local `dualMap Q a` is the genuine
continuous composite `a.comp Q`, with a definitional evaluation lemma.
-/

namespace BlockMassPullback

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Y : Type v} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The complete continuous dual as a type, with no restriction to an adjoint range. -/
abbrev Dual (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := E →L[ℝ] ℝ

abbrev Graph (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  Set (E × Dual E)

/-- The frozen bracket `<z-x,p-a>`: evaluation of `p-a` at `z-x`. -/
def gap (z w : E × Dual E) : ℝ := (z.2 - w.2) (z.1 - w.1)

/-- Quantification is over every row and every label of the graph. -/
def polar (G : Graph E) : Graph E := {z | ∀ w ∈ G, 0 ≤ gap z w}

def GraphMonotone (G : Graph E) : Prop := ∀ z ∈ G, ∀ w ∈ G, 0 ≤ gap z w

/-- Standard maximality: monotonicity and no proper monotone extension in `E × Dual E`. -/
def MaximalMonotone (G : Graph E) : Prop :=
  GraphMonotone G ∧ ∀ H : Graph E, G ⊆ H → GraphMonotone H → H = G

@[simp] theorem gap_self (z : E × Dual E) : gap z z = 0 := by
  simp [gap]

theorem gap_comm (z w : E × Dual E) : gap z w = gap w z := by
  simp only [gap, ContinuousLinearMap.sub_apply, map_sub]
  ring

theorem monotone_iff_subset_polar (G : Graph E) : GraphMonotone G ↔ G ⊆ polar G :=
  Iff.rfl

theorem monotone_insert_iff (G : Graph E) (z : E × Dual E) :
    GraphMonotone (insert z G) ↔ GraphMonotone G ∧ z ∈ polar G := by
  constructor
  · intro h
    constructor
    · intro x hx y hy
      exact h x (Set.mem_insert_of_mem z hx) y (Set.mem_insert_of_mem z hy)
    · intro y hy
      exact h z (Set.mem_insert z G) y (Set.mem_insert_of_mem z hy)
  · rintro ⟨hG, hz⟩ x hx y hy
    rcases Set.mem_insert_iff.mp hx with rfl | hxG
    · rcases Set.mem_insert_iff.mp hy with rfl | hyG
      · simp
      · exact hz y hyG
    · rcases Set.mem_insert_iff.mp hy with rfl | hyG
      · rw [gap_comm]
        exact hz x hxG
      · exact hG x hxG y hyG

/-- This is a proved equivalence, not a replacement of maximality by an assumption. -/
theorem maximal_iff_monotone_polar_subset (G : Graph E) :
    MaximalMonotone G ↔ GraphMonotone G ∧ polar G ⊆ G := by
  constructor
  · rintro ⟨hmono, hmax⟩
    refine ⟨hmono, ?_⟩
    intro z hz
    have heq := hmax (insert z G) (Set.subset_insert z G)
      ((monotone_insert_iff G z).mpr ⟨hmono, hz⟩)
    rw [← heq]
    exact Set.mem_insert z G
  · rintro ⟨hmono, hpolar⟩
    refine ⟨hmono, ?_⟩
    intro H hGH hH
    apply Set.Subset.antisymm _ hGH
    intro z hz
    exact hpolar (fun w hw => hH z hz w (hGH hw))

theorem maximal_iff_eq_polar (G : Graph E) : MaximalMonotone G ↔ G = polar G := by
  rw [maximal_iff_monotone_polar_subset, monotone_iff_subset_polar]
  exact ⟨fun h => Set.Subset.antisymm h.1 h.2,
    fun h => ⟨h.subset, h.symm.subset⟩⟩

/-- Local compatibility name for the actual continuous adjoint action. -/
def dualMap (Q : E →L[ℝ] Y) (a : Dual Y) : Dual E := a.comp Q

@[simp] theorem dualMap_apply (Q : E →L[ℝ] Y) (a : Dual Y) (x : E) :
    dualMap Q a x = a (Q x) := rfl

/-- The entire graph `{(u,Q* a) | (Q u,a) ∈ G}`, including all kernel translates. -/
def pullback (Q : E →L[ℝ] Y) (G : Graph Y) : Graph E :=
  {z | ∃ a : Dual Y, (Q z.1, a) ∈ G ∧ z.2 = dualMap Q a}

@[simp] theorem mem_pullback_iff (Q : E →L[ℝ] Y) (G : Graph Y)
    (x : E) (p : Dual E) :
    (x, p) ∈ pullback Q G ↔ ∃ a : Dual Y, (Q x, a) ∈ G ∧ p = dualMap Q a := Iff.rfl

theorem gap_pullback (Q : E →L[ℝ] Y) (x y : E) (a b : Dual Y) :
    gap (x, dualMap Q a) (y, dualMap Q b) = gap (Q x, a) (Q y, b) := by
  simp [gap, map_sub]

theorem monotone_pullback (Q : E →L[ℝ] Y) {G : Graph Y}
    (hG : GraphMonotone G) : GraphMonotone (pullback Q G) := by
  rintro ⟨x, p⟩ ⟨a, ha, rfl⟩ ⟨y, q⟩ ⟨b, hb, rfl⟩
  rw [gap_pullback]
  exact hG (Q x, a) ha (Q y, b) hb

theorem pullback_nonempty (Q : E →L[ℝ] Y) (hQ : Function.Surjective Q)
    {G : Graph Y} (hne : G.Nonempty) : (pullback Q G).Nonempty := by
  obtain ⟨⟨y, a⟩, ha⟩ := hne
  obtain ⟨x, hx⟩ := hQ y
  exact ⟨(x, dualMap Q a), a, by simpa only [hx] using ha, rfl⟩

theorem kernel_line_mem (Q : E →L[ℝ] Y) {G : Graph Y} {x : E} {a : Dual Y}
    (ha : (Q x, a) ∈ G) {k : E} (hk : Q k = 0) (t : ℝ) :
    (x + t • k, dualMap Q a) ∈ pullback Q G := by
  refine ⟨a, ?_, rfl⟩
  simpa only [map_add, map_smul, hk, smul_zero, add_zero] using ha

/-- An arbitrary full-dual polar label annihilates the kernel, by all real line tests.
Neither maximality nor membership of the label in the adjoint range is assumed. -/
theorem polar_annihilates_kernel (Q : E →L[ℝ] Y) (hQ : Function.Surjective Q)
    {G : Graph Y} (hne : G.Nonempty) {z : E} {p : Dual E}
    (hpolar : (z, p) ∈ polar (pullback Q G)) : ∀ k : E, Q k = 0 → p k = 0 := by
  obtain ⟨⟨y, a⟩, ha⟩ := hne
  obtain ⟨x, hx⟩ := hQ y
  have hrow : (Q x, a) ∈ G := by simpa only [hx] using ha
  intro k hk
  have hline (t : ℝ) := hpolar (x + t • k, dualMap Q a) (kernel_line_mem Q hrow hk t)
  have hexpand (t : ℝ) :
      gap (z, p) (x + t • k, dualMap Q a) = gap (z, p) (x, dualMap Q a) - t * p k := by
    simp [gap, map_sub, map_add, map_smul, hk]
    ring
  by_contra hpk
  have h := hline ((gap (z, p) (x, dualMap Q a) + 1) / p k)
  rw [hexpand, div_mul_cancel₀ _ hpk] at h
  linarith

/-- Quantitative intermediate step: annihilation plus an explicit norm lift
constructs a functional in the continuous dual of `Y`, with its bound proved. -/
theorem exists_dual_factor_of_norm_lift (Q : E →L[ℝ] Y) (hQ : Function.Surjective Q)
    (p : Dual E) (hker : ∀ k : E, Q k = 0 → p k = 0)
    (C : ℝ) (hlift : ∀ y : Y, ∃ x : E, Q x = y ∧ ‖x‖ ≤ C * ‖y‖) :
    ∃ a : Dual Y, dualMap Q a = p := by
  classical
  let s : Y → E := fun y => Classical.choose (hQ y)
  have hs (y : Y) : Q (s y) = y := Classical.choose_spec (hQ y)
  have hsame (x x' : E) (heq : Q x = Q x') : p x = p x' := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply hker
    rw [map_sub, heq, sub_self]
  let f : Y →ₗ[ℝ] ℝ := {
    toFun := fun y => p (s y)
    map_add' := by
      intro y y'
      change p (s (y + y')) = p (s y) + p (s y')
      rw [← map_add]
      apply hsame
      simp only [hs, map_add]
    map_smul' := by
      intro c y
      change p (s (c • y)) = c • p (s y)
      rw [← map_smul]
      apply hsame
      simp only [hs, map_smul] }
  have hbound (y : Y) : ‖f y‖ ≤ (‖p‖ * C) * ‖y‖ := by
    obtain ⟨x, hx, hnorm⟩ := hlift y
    have heval : f y = p x := hsame (s y) x (by rw [hs, hx])
    rw [heval]
    calc
      ‖p x‖ ≤ ‖p‖ * ‖x‖ := p.le_opNorm x
      _ ≤ ‖p‖ * (C * ‖y‖) := mul_le_mul_of_nonneg_left hnorm (norm_nonneg p)
      _ = (‖p‖ * C) * ‖y‖ := (mul_assoc _ _ _).symm
  refine ⟨f.mkContinuous (‖p‖ * C) hbound, ?_⟩
  ext x
  change p (s (Q x)) = p x
  exact hsame (s (Q x)) x (hs (Q x))

/-- The extra quantitative premise is discharged by mathlib's Banach open mapping theorem. -/
theorem exists_dual_factor [CompleteSpace E] [CompleteSpace Y]
    (Q : E →L[ℝ] Y) (hQ : Function.Surjective Q)
    (p : Dual E) (hker : ∀ k : E, Q k = 0 → p k = 0) :
    ∃ a : Dual Y, dualMap Q a = p := by
  obtain ⟨C, _, hlift⟩ := Q.exists_preimage_norm_le hQ
  exact exists_dual_factor_of_norm_lift Q hQ p hker C hlift

/-- The descent identity allows testing every original graph row using surjectivity. -/
theorem polar_descends (Q : E →L[ℝ] Y) (hQ : Function.Surjective Q)
    {G : Graph Y} {z : E} {a : Dual Y}
    (hpolar : (z, dualMap Q a) ∈ polar (pullback Q G)) : (Q z, a) ∈ polar G := by
  rintro ⟨y, b⟩ hb
  obtain ⟨x, hx⟩ := hQ y
  have hrow : (x, dualMap Q b) ∈ pullback Q G :=
    ⟨b, by simpa only [hx] using hb, rfl⟩
  have h := hpolar (x, dualMap Q b) hrow
  rw [gap_pullback, hx] at h
  exact h

/-- All full-dual polar points of the pullback are actual graph rows. -/
theorem polar_pullback_subset [CompleteSpace E] [CompleteSpace Y]
    (Q : E →L[ℝ] Y) (hQ : Function.Surjective Q)
    {G : Graph Y} (hne : G.Nonempty) (hG : MaximalMonotone G) :
    polar (pullback Q G) ⊆ pullback Q G := by
  rintro ⟨z, p⟩ hp
  have hker := polar_annihilates_kernel Q hQ hne hp
  obtain ⟨a, ha⟩ := exists_dual_factor Q hQ p hker
  have hpa : (z, dualMap Q a) ∈ polar (pullback Q G) := by simpa only [ha] using hp
  have hdown := polar_descends Q hQ hpa
  have hmem := ((maximal_iff_monotone_polar_subset G).mp hG).2 hdown
  exact ⟨a, hmem, ha.symm⟩

/-- Generic r1 L2 transport theorem in real Banach spaces and their full continuous duals.
Surjectivity is the only map hypothesis beyond bundled continuous linearity.
This auxiliary theorem does not certify a BlockMass counterexample. -/
theorem maximalMonotone_pullback [CompleteSpace E] [CompleteSpace Y]
    (Q : E →L[ℝ] Y) (hQ : Function.Surjective Q)
    {G : Graph Y} (hne : G.Nonempty) (hG : MaximalMonotone G) :
    MaximalMonotone (pullback Q G) := by
  apply (maximal_iff_monotone_polar_subset (pullback Q G)).mpr
  exact ⟨monotone_pullback Q hG.1, polar_pullback_subset Q hQ hne hG⟩

end BlockMassPullback

#print axioms BlockMassPullback.maximal_iff_monotone_polar_subset
#print axioms BlockMassPullback.maximal_iff_eq_polar
#print axioms BlockMassPullback.polar_annihilates_kernel
#print axioms BlockMassPullback.exists_dual_factor_of_norm_lift
#print axioms BlockMassPullback.exists_dual_factor
#print axioms BlockMassPullback.polar_descends
#print axioms BlockMassPullback.polar_pullback_subset
#print axioms BlockMassPullback.maximalMonotone_pullback
