import BlockMassRankOne

/-!
Generic last-step graph-sum interface only. Actual maximality,
nonempty domain, missing zero and the all-row work inequality for the constructed
first factor remain required inputs, not assumed conclusions of the sum problem.
-/

noncomputable section
open BlockMassRankOne

namespace BlockMassSumWitness

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def graphDomain (G : Set (X × NormedSpace.Dual ℝ X)) : Set X :=
  {x | ∃ p, (x,p) ∈ G}

/-- Pointwise operator sum: both labels are taken at the SAME primal point. -/
def graphSum (G H : Set (X × NormedSpace.Dual ℝ X)) :
    Set (X × NormedSpace.Dual ℝ X) :=
  {u | ∃ a b, (u.1,a) ∈ G ∧ (u.1,b) ∈ H ∧ u.2 = a+b}

theorem graphSum_monotone (G H : Set (X × NormedSpace.Dual ℝ X))
    (hG : GraphMonotone G) (hH : GraphMonotone H) :
    GraphMonotone (graphSum G H) := by
  rintro ⟨x,p⟩ ⟨a,b,ha,hb,hp⟩ ⟨y,q⟩ ⟨c,d,hc,hd,hq⟩
  change p = a+b at hp
  change q = c+d at hq
  subst p
  subst q
  have h1 := hG (x,a) ha (y,c) hc
  have h2 := hH (x,b) hb (y,d) hd
  simp only [bracket, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply] at h1 h2 ⊢
  linarith

theorem rankOne_domain (g : NormedSpace.Dual ℝ X) :
    graphDomain (rankOneGraph g) = Set.univ := by
  ext x
  simp only [graphDomain, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact ⟨rankOne g x, rfl⟩

theorem rankOne_ordered_CQ (G : Set (X × NormedSpace.Dual ℝ X))
    (g : NormedSpace.Dual ℝ X) (hne : G.Nonempty) :
    (graphDomain G ∩ interior (graphDomain (rankOneGraph g))).Nonempty := by
  obtain ⟨⟨x,p⟩,hp⟩ := hne
  rw [rankOne_domain, interior_univ, Set.inter_univ]
  exact ⟨x,p,hp⟩

theorem zero_polar_of_self_work (G : Set (X × NormedSpace.Dual ℝ X))
    (hwork : ∀ u ∈ G, 0 ≤ u.2 u.1) :
    ((0 : X),(0 : NormedSpace.Dual ℝ X)) ∈ monotonePolar G := by
  intro u hu
  simpa [bracket] using hwork u hu

theorem rankOne_sum_self_work (G : Set (X × NormedSpace.Dual ℝ X))
    (g : NormedSpace.Dual ℝ X)
    (hwork : ∀ x a, (x,a) ∈ G → 0 ≤ a x + (g x)^2) :
    ∀ u ∈ graphSum G (rankOneGraph g), 0 ≤ u.2 u.1 := by
  rintro ⟨x,p⟩ ⟨a,b,ha,hb,hp⟩
  change p = a+b at hp
  subst p
  have hb' : b = rankOne g x := hb
  simp only [hb', ContinuousLinearMap.add_apply, rankOne_apply_apply]
  simpa only [pow_two] using hwork x a ha

theorem zero_missing_from_sum (G H : Set (X × NormedSpace.Dual ℝ X))
    (hzero : (0 : X) ∉ graphDomain G) :
    ((0 : X),(0 : NormedSpace.Dual ℝ X)) ∉ graphSum G H := by
  rintro ⟨a,b,ha,_,_⟩
  exact hzero ⟨a,ha⟩

theorem nonmaximal_of_polar_nongraph (G : Set (X × NormedSpace.Dual ℝ X))
    (u : X × NormedSpace.Dual ℝ X) (hp : u ∈ monotonePolar G)
    (hn : u ∉ G) : ¬ MaximallyMonotone G := by
  intro hmax
  rw [(maximallyMonotone_iff_polar_eq G).mp hmax] at hp
  exact hn hp

/-- Compiler of the final witness obligations, NOT a constructed instance. -/
theorem rankOne_sum_certificate (G : Set (X × NormedSpace.Dual ℝ X))
    (g : NormedSpace.Dual ℝ X) (hmax : MaximallyMonotone G)
    (hne : G.Nonempty) (hzero : (0 : X) ∉ graphDomain G)
    (hwork : ∀ x a, (x,a) ∈ G → 0 ≤ a x + (g x)^2) :
    MaximallyMonotone G ∧ MaximallyMonotone (rankOneGraph g) ∧
    (graphDomain G ∩ interior (graphDomain (rankOneGraph g))).Nonempty ∧
    GraphMonotone (graphSum G (rankOneGraph g)) ∧
    ((0 : X),(0 : NormedSpace.Dual ℝ X)) ∈ monotonePolar (graphSum G (rankOneGraph g)) ∧
    ((0 : X),(0 : NormedSpace.Dual ℝ X)) ∉ graphSum G (rankOneGraph g) ∧
    ¬ MaximallyMonotone (graphSum G (rankOneGraph g)) := by
  have hp := zero_polar_of_self_work _ (rankOne_sum_self_work G g hwork)
  have hn := zero_missing_from_sum G (rankOneGraph g) hzero
  exact ⟨hmax, rankOne_maximally_monotone g, rankOne_ordered_CQ G g hne,
    graphSum_monotone G _ hmax.1 (rankOne_graph_monotone g), hp, hn,
    nonmaximal_of_polar_nongraph _ _ hp hn⟩

end BlockMassSumWitness

#print axioms BlockMassSumWitness.graphSum_monotone
#print axioms BlockMassSumWitness.rankOne_domain
#print axioms BlockMassSumWitness.rankOne_ordered_CQ
#print axioms BlockMassSumWitness.zero_polar_of_self_work
#print axioms BlockMassSumWitness.rankOne_sum_self_work
#print axioms BlockMassSumWitness.zero_missing_from_sum
#print axioms BlockMassSumWitness.nonmaximal_of_polar_nongraph
#print axioms BlockMassSumWitness.rankOne_sum_certificate
