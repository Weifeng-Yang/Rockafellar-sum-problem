import BlockMassC0Dual
import BlockMassTriangular
import BlockMassCurve
import BlockMassRankOne

/-!
Actual Banach graph/algebra bridge only.
Y is the existing complete normed c0 model; labels are its FULL continuous dual.
No maximality, polar classification, sum theorem or counterexample is asserted.
Frozen source index (b,j>=1) corresponds to Lean (b,j-1).
-/

open scoped BigOperators Topology

noncomputable section
namespace BlockMassGraphModel

abbrev Index := BlockMassC0Dual.Index
abbrev Y := BlockMassC0Dual.Y
abbrev Dual := NormedSpace.Dual ℝ Y
abbrev coords := BlockMassC0Dual.coordinates

theorem coords_absSummable (p : Dual) : BlockMassTriangular.AbsSummable (coords p) :=
  BlockMassC0Dual.coordinates_absSummable p

theorem coords_injective : Function.Injective coords := by
  intro p q hpq
  exact BlockMassC0Dual.fullDualEquiv.injective (Subtype.ext hpq)

@[simp] theorem coords_add (p q : Dual) : coords (p + q) = coords p + coords q := rfl
@[simp] theorem coords_sub (p q : Dual) : coords (p - q) = coords p - coords q := rfl
@[simp] theorem coords_neg (p : Dual) : coords (-p) = -coords p := rfl
@[simp] theorem coords_smul (s : ℝ) (p : Dual) : coords (s • p) = s • coords p := rfl
@[simp] theorem coords_zero : coords (0 : Dual) = 0 := rfl

def E (p : Dual) : Y := BlockMassC0Dual.ofGlobal
  (BlockMassTriangular.blockE (coords p))
  (BlockMassTriangular.blockE_globalC0 (coords_absSummable p))

@[simp] theorem E_apply (p : Dual) (i : Index) :
    E p i = BlockMassTriangular.blockE (coords p) i := rfl

def mass (p : Dual) : ℕ → ℝ := BlockMassTriangular.m (coords p)
def r (p : Dual) : ℝ := -coords p (0, 0) - coords p (0, 1)
def h : Y := -BlockMassC0Dual.basis (0, 0) - BlockMassC0Dual.basis (0, 1)
def L (p : Dual) : Y := -E p + r p • h

theorem mass_absSummable (p : Dual) : BlockMassTriangular.AbsSummable (mass p) :=
  BlockMassTriangular.m_absSummable (coords_absSummable p)

@[simp] theorem mass_add (p q : Dual) : mass (p + q) = mass p + mass q :=
  BlockMassTriangular.m_add (coords_absSummable p) (coords_absSummable q)

@[simp] theorem mass_smul (s : ℝ) (p : Dual) : mass (s • p) = s • mass p :=
  BlockMassTriangular.m_smul (coords p) s

@[simp] theorem mass_neg (p : Dual) : mass (-p) = -mass p := by
  simpa using mass_smul (-1) p

@[simp] theorem mass_sub (p q : Dual) : mass (p - q) = mass p - mass q := by
  simp only [sub_eq_add_neg, mass_add, mass_neg]

@[simp] theorem mass_zero : mass (0 : Dual) = 0 := by
  funext b
  simp [mass, BlockMassTriangular.m, BlockMassTriangular.mass, coords_zero]

@[simp] theorem r_add (p q : Dual) : r (p + q) = r p + r q := by
  simp [r, coords_add]; ring
@[simp] theorem r_sub (p q : Dual) : r (p - q) = r p - r q := by
  simp [r, coords_sub]; ring
@[simp] theorem r_smul (s : ℝ) (p : Dual) : r (s • p) = s * r p := by
  simp [r, coords_smul]; ring
@[simp] theorem r_zero : r (0 : Dual) = 0 := by simp [r]

@[simp] theorem E_add (p q : Dual) : E (p + q) = E p + E q := by
  ext i
  exact congrFun (BlockMassTriangular.blockE_add (coords_absSummable p)
    (coords_absSummable q)) i

@[simp] theorem E_smul (s : ℝ) (p : Dual) : E (s • p) = s • E p := by
  ext i
  exact congrFun (BlockMassTriangular.blockE_smul (coords p) s) i

@[simp] theorem E_neg (p : Dual) : E (-p) = -E p := by
  ext i
  have hi := congrArg (fun x : Y => x i) (E_smul (-1) p)
  simpa only [neg_one_smul, ZeroAtInftyContinuousMap.smul_apply,
    ZeroAtInftyContinuousMap.neg_apply, smul_eq_mul, neg_mul, one_mul] using hi

@[simp] theorem E_sub (p q : Dual) : E (p - q) = E p - E q := by
  simp only [sub_eq_add_neg, E_add, E_neg]

@[simp] theorem L_sub (p q : Dual) : L (p - q) = L p - L q := by
  ext i
  simp only [L, E_sub, r_sub, ZeroAtInftyContinuousMap.add_apply,
    ZeroAtInftyContinuousMap.neg_apply, ZeroAtInftyContinuousMap.sub_apply,
    ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul]
  ring

@[simp] theorem apply_h (p : Dual) : p h = r p := by
  simp [h, r, coords, BlockMassC0Dual.coordinates]

theorem E_pairing (p q : Dual) :
    q (E p) = BlockMassTriangular.pairing (BlockMassTriangular.blockE (coords p))
      (coords q) := BlockMassC0Dual.functional_eq_tsum q (E p)

theorem E_symmetric_work (p q : Dual) :
    q (E p) + p (E q) = 2 * ∑' b, mass p b * mass q b := by
  rw [E_pairing, E_pairing]
  exact BlockMassTriangular.blockE_symmetric_identity
    (coords_absSummable p) (coords_absSummable q)

theorem mass_square_summable (p : Dual) : Summable (fun b => (mass p b) ^ 2) :=
  BlockMassTriangular.m_square_summable (coords_absSummable p)

theorem E_quadratic_work (p : Dual) : p (E p) = ∑' b, (mass p b) ^ 2 := by
  rw [E_pairing]
  exact BlockMassTriangular.blockE_quadratic_identity (coords_absSummable p)

theorem L_work (p : Dual) : p (L p) = (r p) ^ 2 - ∑' b, (mass p b) ^ 2 := by
  simp only [L, map_add, map_neg, map_smul, smul_eq_mul, apply_h, E_quadratic_work]
  ring

theorem L_difference_work (p q : Dual) :
    (p - q) (L p - L q) = (r p - r q) ^ 2 - ∑' b, (mass p b - mass q b) ^ 2 := by
  rw [← L_sub, L_work, r_sub, mass_sub]
  rfl

theorem mass_difference_square_summable (p q : Dual) :
    Summable (fun b => (mass p b - mass q b) ^ 2) := by
  simpa only [mass_sub, Pi.sub_apply] using mass_square_summable (p - q)

/-- The coefficient delta is truly absolutely summable. -/
def delta (i : Index) (j : Index) : ℝ := if j = i then 1 else 0

theorem delta_absSummable (i : Index) : BlockMassC0Dual.AbsSummable (delta i) := by
  classical
  apply Summable.abs
  exact summable_of_ne_finset_zero (s := {i}) (by
    intro j hj
    simp only [Finset.mem_singleton] at hj
    simp [delta, hj])

/-- Unit coordinate functional, constructed by the proved ell1/full-dual map. -/
def unitDual (i : Index) : Dual := BlockMassC0Dual.ofAbsSummable (delta i) (delta_absSummable i)

@[simp] theorem coords_unitDual (i : Index) : coords (unitDual i) = delta i :=
  BlockMassC0Dual.coordinates_ofAbsSummable _ _

@[simp] theorem unitDual_apply (i : Index) (x : Y) : unitDual i x = x i := by
  classical
  change (∑' j, x j * delta i j) = x i
  rw [tsum_eq_single i]
  · simp [delta]
  · intro j hji; simp [delta, hji]

def g : Dual := unitDual (0, 0) - unitDual (0, 1)

@[simp] theorem g_apply (x : Y) : g x = x (0, 0) - x (0, 1) := by
  simp [g]

theorem E_unitDual (i j : Index) :
    E (unitDual i) j = if j.1 = i.1 then BlockMassTriangular.weight j.2 i.2 else 0 := by
  classical
  rw [E_apply, coords_unitDual]
  unfold BlockMassTriangular.blockE
  rw [BlockMassTriangular.E_eq_kernel
    (BlockMassTriangular.block_absSummable (delta_absSummable i) j.1)]
  by_cases hb : j.1 = i.1
  · rw [tsum_eq_single i.2]
    · simp [delta, Prod.ext_iff, hb]
    · intro k hk; simp [delta, Prod.ext_iff, hk]
  · simp [delta, Prod.ext_iff, hb]

@[simp] theorem E_g : E g = h := by
  ext ⟨b, j⟩
  simp only [g, E_sub, ZeroAtInftyContinuousMap.sub_apply, E_unitDual,
    h, ZeroAtInftyContinuousMap.neg_apply, BlockMassC0Dual.basis_apply]
  by_cases hb : b = 0
  · subst b
    rcases j with _ | j
    · norm_num [BlockMassTriangular.weight, Prod.ext_iff]
    · rcases j with _ | j
      · norm_num [BlockMassTriangular.weight]
      · simp [BlockMassTriangular.weight]
  · simp [hb, Prod.ext_iff]

@[simp] theorem r_g : r g = 0 := by
  simp [r, g, coords_unitDual, delta, Prod.ext_iff]

theorem mass_unitDual (i : Index) (b : ℕ) :
    mass (unitDual i) b = if b = i.1 then 1 else 0 := by
  classical
  by_cases hb : b = i.1 <;>
    simp [mass, BlockMassTriangular.m, BlockMassTriangular.mass,
      coords_unitDual, delta, Prod.ext_iff, hb]

@[simp] theorem mass_g : mass g = 0 := by
  funext b
  simp [g, mass_unitDual]

@[simp] theorem g_E (p : Dual) : g (E p) = -r p := by
  have he := E_symmetric_work p g
  simp only [E_g, apply_h, mass_g, Pi.zero_apply, mul_zero, tsum_zero] at he
  linarith

@[simp] theorem g_L (p : Dual) : g (L p) = r p := by
  simp only [L, map_add, map_neg, map_smul, smul_eq_mul, g_E, apply_h, r_g,
    mul_zero, add_zero, neg_neg]

/-- C2 for arbitrary, genuinely absolutely summable coordinate inputs. -/
theorem coordinate_difference_work (a c : Index → ℝ)
    (ha : BlockMassC0Dual.AbsSummable a) (hc : BlockMassC0Dual.AbsSummable c) :
    let p := BlockMassC0Dual.ofAbsSummable a ha
    let q := BlockMassC0Dual.ofAbsSummable c hc
    (p - q) (L p - L q) =
      ((-a (0, 0) - a (0, 1)) - (-c (0, 0) - c (0, 1))) ^ 2 -
      ∑' b, (BlockMassTriangular.m a b - BlockMassTriangular.m c b) ^ 2 := by
  dsimp only
  simpa only [r, mass, coords, BlockMassC0Dual.coordinates_ofAbsSummable] using
    L_difference_work (BlockMassC0Dual.ofAbsSummable a ha)
      (BlockMassC0Dual.ofAbsSummable c hc)

/-- Actual labels, in the full continuous dual, not a formal label type. -/
def D : Set Dual := {p | BlockMassCurve.Actual (r p) ∧ mass p = BlockMassCurve.wholeF (r p)}

/-- A genuine subset of Y times its complete continuous dual. -/
def graphA : Set (Y × Dual) := {u | ∃ p ∈ D, u = (L p, p)}

theorem graphA_monotone : BlockMassRankOne.GraphMonotone graphA := by
  rintro u ⟨p, hp, rfl⟩ v ⟨q, hq, rfl⟩
  change 0 ≤ (p - q) (L p - L q)
  rw [L_difference_work, hp.2, hq.2]
  exact sub_nonneg.mpr (BlockMassCurve.wholeF_sq_lipschitz (r p) (r q) hp.1 hq.1)

/-- Exact coordinate-set presentation requested in D7/D8. No labels are omitted. -/
theorem mem_graphA_iff_coordinates (u : Y × Dual) : u ∈ graphA ↔
    ∃ (a : Index → ℝ) (ha : BlockMassC0Dual.AbsSummable a),
      BlockMassCurve.Actual (-a (0, 0) - a (0, 1)) ∧
      BlockMassTriangular.m a = BlockMassCurve.wholeF (-a (0, 0) - a (0, 1)) ∧
      u = (L (BlockMassC0Dual.ofAbsSummable a ha), BlockMassC0Dual.ofAbsSummable a ha) := by
  constructor
  · rintro ⟨p, hp, hu⟩
    refine ⟨coords p, BlockMassC0Dual.coordinates_absSummable p, hp.1, hp.2, ?_⟩
    simpa only [coords, BlockMassC0Dual.ofAbsSummable_coordinates] using hu
  · rintro ⟨a, ha, hr, hm, hu⟩
    refine ⟨BlockMassC0Dual.ofAbsSummable a ha, ?_, hu⟩
    simpa only [D, Set.mem_setOf_eq, r, mass, coords,
      BlockMassC0Dual.coordinates_ofAbsSummable] using And.intro hr hm

/-- Put each block mass in that block's first coordinate. -/
def liftCoeff (f : ℕ → ℝ) (i : Index) : ℝ := if i.2 = 0 then f i.1 else 0

theorem liftCoeff_finite_support (f : ℕ → ℝ) (hf : (Function.support f).Finite) :
    (Function.support (liftCoeff f)).Finite := by
  apply (hf.image (fun b : ℕ => (b, 0))).subset
  rintro ⟨b, j⟩ hi
  by_cases hj : j = 0
  · refine ⟨b, ?_, by simp [hj]⟩
    simpa [Function.mem_support, liftCoeff, hj] using hi
  · simp [Function.mem_support, liftCoeff, hj] at hi

theorem mass_liftCoeff (f : ℕ → ℝ) : BlockMassTriangular.m (liftCoeff f) = f := by
  funext b
  simp [BlockMassTriangular.m, BlockMassTriangular.mass, liftCoeff]

/-- Exact D9 label, written as a finite mass lift and a zero-mass correction. -/
def sectionCoords (t : ℝ) (i : Index) : ℝ :=
  liftCoeff (BlockMassCurve.wholeF t) i - (t + Real.sign t) * delta (0, 0) i +
    (t + Real.sign t) * delta (0, 2) i

theorem sectionCoords_formula (t : ℝ) (b j : ℕ) :
    sectionCoords t (b, j) =
      -t * delta (0, 0) (b, j) + (t + Real.sign t) * delta (0, 2) (b, j) +
        if b = 0 then 0 else if j = 0 then BlockMassCurve.omega (|t| - 1) (b - 1) else 0 := by
  cases b with
  | zero =>
    by_cases hj : j = 0 <;>
      simp [sectionCoords, liftCoeff, delta, Prod.ext_iff, BlockMassCurve.wholeF, hj]
  | succ b =>
    simp [sectionCoords, liftCoeff, delta, Prod.ext_iff, BlockMassCurve.wholeF]

theorem sectionCoords_finite_support (t : ℝ) (ht : BlockMassCurve.Actual t) :
    (Function.support (sectionCoords t)).Finite := by
  classical
  apply ((liftCoeff_finite_support _ (BlockMassCurve.wholeF_finite_support t ht)).union
    ((Set.finite_singleton (0, 2)).insert (0, 0))).subset
  intro i hi
  by_contra hn
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    not_or, Function.mem_support, not_not] at hn
  exact hi (by simp only [sectionCoords, hn.1, delta, if_neg hn.2.1, if_neg hn.2.2,
    mul_zero, sub_zero, add_zero])

theorem sectionCoords_absSummable (t : ℝ) (ht : BlockMassCurve.Actual t) :
    BlockMassC0Dual.AbsSummable (sectionCoords t) :=
  (summable_of_finite_support (sectionCoords_finite_support t ht)).abs

def sectionLabel (t : ℝ) (ht : BlockMassCurve.Actual t) : Dual :=
  BlockMassC0Dual.ofAbsSummable (sectionCoords t) (sectionCoords_absSummable t ht)

@[simp] theorem coords_sectionLabel (t : ℝ) (ht : BlockMassCurve.Actual t) :
    coords (sectionLabel t ht) = sectionCoords t :=
  BlockMassC0Dual.coordinates_ofAbsSummable _ _

@[simp] theorem r_sectionLabel (t : ℝ) (ht : BlockMassCurve.Actual t) :
    r (sectionLabel t ht) = t := by
  simp [r, coords_sectionLabel, sectionCoords, liftCoeff, delta,
    Prod.ext_iff, BlockMassCurve.wholeF]

theorem sectionLabel_decomposition (t : ℝ) (ht : BlockMassCurve.Actual t) :
    sectionLabel t ht =
      BlockMassC0Dual.ofAbsSummable (liftCoeff (BlockMassCurve.wholeF t))
        (summable_of_finite_support (liftCoeff_finite_support _
          (BlockMassCurve.wholeF_finite_support t ht))).abs -
      (t + Real.sign t) • unitDual (0, 0) + (t + Real.sign t) • unitDual (0, 2) := by
  apply coords_injective
  funext i
  simp only [coords_sectionLabel, coords_add,
    coords_sub, coords_smul, coords_unitDual, sectionCoords,
    BlockMassC0Dual.coordinates_ofAbsSummable, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]

@[simp] theorem mass_sectionLabel (t : ℝ) (ht : BlockMassCurve.Actual t) :
    mass (sectionLabel t ht) = BlockMassCurve.wholeF t := by
  rw [sectionLabel_decomposition, mass_add, mass_sub, mass_smul, mass_smul]
  funext b
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mass_unitDual]
  have hl : mass (BlockMassC0Dual.ofAbsSummable (liftCoeff (BlockMassCurve.wholeF t))
      (summable_of_finite_support (liftCoeff_finite_support _
        (BlockMassCurve.wholeF_finite_support t ht))).abs) b = BlockMassCurve.wholeF t b := by
    simp only [mass, coords, BlockMassC0Dual.coordinates_ofAbsSummable, mass_liftCoeff]
  rw [hl]
  ring

theorem sectionLabel_mem_D (t : ℝ) (ht : BlockMassCurve.Actual t) :
    sectionLabel t ht ∈ D := by
  simp only [D, Set.mem_setOf_eq, r_sectionLabel, mass_sectionLabel, and_true]
  exact ht

theorem D_nonempty : D.Nonempty :=
  ⟨sectionLabel 2 (Or.inr (by norm_num)), sectionLabel_mem_D 2 (Or.inr (by norm_num))⟩

theorem graphA_nonempty : graphA.Nonempty := by
  obtain ⟨p, hp⟩ := D_nonempty
  exact ⟨(L p, p), p, hp, rfl⟩

/-- Our own full-dual kernel. No annihilator theorem is assumed or imported. -/
def K : Set Dual := {k | mass k = 0 ∧ r k = 0}

theorem mem_fibre_iff (t : ℝ) (ht : BlockMassCurve.Actual t) (p : Dual) :
    (r p = t ∧ mass p = BlockMassCurve.wholeF t) ↔
      ∃ k ∈ K, p = sectionLabel t ht + k := by
  constructor
  · rintro ⟨hr, hm⟩
    refine ⟨p - sectionLabel t ht, ?_, by abel⟩
    simp only [K, Set.mem_setOf_eq, mass_sub, mass_sectionLabel, r_sub, r_sectionLabel,
      hr, hm, sub_self, and_self]
  · rintro ⟨k, ⟨hm, hr⟩, rfl⟩
    simp only [r_add, r_sectionLabel, hr, add_zero, mass_add, mass_sectionLabel, hm,
      and_self]

theorem fibre_eq_translate (t : ℝ) (ht : BlockMassCurve.Actual t) :
    {p : Dual | r p = t ∧ mass p = BlockMassCurve.wholeF t} =
      (fun k => sectionLabel t ht + k) '' K := by
  ext p
  simpa only [Set.mem_setOf_eq, Set.mem_image, eq_comm] using mem_fibre_iff t ht p

theorem D_fibre_eq_translate (t : ℝ) (ht : BlockMassCurve.Actual t) :
    {p : Dual | p ∈ D ∧ r p = t} = (fun k => sectionLabel t ht + k) '' K := by
  rw [← fibre_eq_translate t ht]
  ext p
  change ((BlockMassCurve.Actual (r p) ∧ mass p = BlockMassCurve.wholeF (r p)) ∧ r p = t) ↔
    r p = t ∧ mass p = BlockMassCurve.wholeF t
  constructor
  · rintro ⟨⟨_, hm⟩, hr⟩
    exact ⟨hr, by simpa only [hr] using hm⟩
  · rintro ⟨hr, hm⟩
    exact ⟨⟨by simpa only [hr] using ht, by simpa only [hr] using hm⟩, hr⟩

/-- The L symmetric identity, with the actual convergent mass product. -/
theorem L_symmetric_work (p q : Dual) :
    q (L p) + p (L q) = 2 * r p * r q - 2 * ∑' b, mass p b * mass q b := by
  simp only [L, map_add, map_neg, map_smul, smul_eq_mul, apply_h]
  linarith [E_symmetric_work p q]

theorem L_pairing_absSummable (p q : Dual) :
    BlockMassTriangular.AbsSummable (fun i => L p i * coords q i) :=
  BlockMassC0Dual.pairing_absSummable (coords q) (coords_absSummable q) (L p)

/-- Literal infinite coordinate pairing, not merely a name for a pairing. -/
theorem L_difference_pairing (p q : Dual) :
    (∑' i, L (p - q) i * (coords p i - coords q i)) =
      (r p - r q) ^ 2 - ∑' b, (mass p b - mass q b) ^ 2 := by
  have hp := BlockMassC0Dual.functional_eq_tsum (p - q) (L (p - q))
  calc
    _ = (p - q) (L (p - q)) := by
      simpa only [coords_sub, Pi.sub_apply] using hp.symm
    _ = _ := by rw [L_sub]; exact L_difference_work p q

end BlockMassGraphModel

#print axioms BlockMassGraphModel.E_symmetric_work
#print axioms BlockMassGraphModel.L_difference_work
#print axioms BlockMassGraphModel.graphA_monotone
