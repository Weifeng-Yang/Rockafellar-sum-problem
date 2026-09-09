import BlockMassPolar
import BlockMassConcreteWitness

/-!
End-to-end assembly for the actual c0 Banach example.
No mathematical hypotheses remain in the certificate theorem below.
Independent final semantic/consumer acceptance remains a separate process.
The standard-ell1 strengthening and optional exact constants are NOT asserted here.
-/

noncomputable section
open scoped Topology

namespace BlockMassCounterexample

open BlockMassGraphModel BlockMassRankOne BlockMassSumWitness
open BlockMassConcreteWitness

/-- The actual first-factor maximality pays the sole input of the concrete assembler. -/
theorem exact_counterexample :
    MaximallyMonotone graphA ∧ MaximallyMonotone (rankOneGraph g) ∧
    (graphDomain graphA ∩ interior (graphDomain (rankOneGraph g))).Nonempty ∧
    GraphMonotone actualSum ∧
    ((0 : Y),(0 : Dual)) ∈ monotonePolar actualSum ∧
    ((0 : Y),(0 : Dual)) ∉ actualSum ∧ ¬ MaximallyMonotone actualSum :=
  conditional_certificate BlockMassPolar.graphA_maximally_monotone

/-- Set-valued operator presentation of the same first graph. -/
def A (x : Y) : Set Dual := {p | (x,p) ∈ graphA}

/-- The everywhere-defined positive nonzero rank-one second operator. -/
def B (x : Y) : Set Dual := {p | p = rankOne g x}

def operatorGraph (T : Y → Set Dual) : Set (Y × Dual) :=
  {u | u.2 ∈ T u.1}

def operatorSum (S T : Y → Set Dual) (x : Y) : Set Dual :=
  {p | ∃ a ∈ S x, ∃ b ∈ T x, p=a+b}

theorem operatorGraph_A : operatorGraph A = graphA := rfl
theorem operatorGraph_B : operatorGraph B = rankOneGraph g := rfl

theorem operator_sum_graph : operatorGraph (operatorSum A B) = actualSum := by
  ext ⟨x,p⟩
  change (∃ a, (x,a) ∈ graphA ∧ ∃ b, b=rankOne g x ∧ p=a+b) ↔
    (∃ a b, (x,a) ∈ graphA ∧ b=rankOne g x ∧ p=a+b)
  constructor
  · rintro ⟨a,ha,b,hb,he⟩
    exact ⟨a,b,ha,hb,he⟩
  · rintro ⟨a,b,ha,hb,he⟩
    exact ⟨a,ha,b,hb,he⟩

/-- Original ordered CQ and actual pointwise operator sum, with no Amax premise. -/
theorem exact_operator_counterexample :
    MaximallyMonotone (operatorGraph A) ∧ MaximallyMonotone (operatorGraph B) ∧
    (graphDomain (operatorGraph A) ∩ interior (graphDomain (operatorGraph B))).Nonempty ∧
    ¬ MaximallyMonotone (operatorGraph (operatorSum A B)) := by
  rw [operatorGraph_A, operatorGraph_B, operator_sum_graph]
  exact ⟨exact_counterexample.1, exact_counterexample.2.1,
    exact_counterexample.2.2.1, actualSum_not_maximal⟩

/-- A formulation over real Banach spaces and their FULL continuous duals.
    A single actual instance suffices to negate the universal claim. -/
def UniversalSumClaim : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (G H : Set (X × NormedSpace.Dual ℝ X)),
    MaximallyMonotone G → MaximallyMonotone H →
    (graphDomain G ∩ interior (graphDomain H)).Nonempty →
    MaximallyMonotone (graphSum G H)

theorem not_universal_sum_claim : ¬ UniversalSumClaim := by
  intro hc
  exact actualSum_not_maximal (hc Y graphA (rankOneGraph g)
    BlockMassPolar.graphA_maximally_monotone actual_rankOne_maximal actual_ordered_CQ)

end BlockMassCounterexample

#synth NormedAddCommGroup BlockMassGraphModel.Y
#synth NormedSpace ℝ BlockMassGraphModel.Y
#synth CompleteSpace BlockMassGraphModel.Y
#check @BlockMassCounterexample.exact_counterexample
#check @BlockMassCounterexample.exact_operator_counterexample
#print BlockMassCounterexample.UniversalSumClaim
#print axioms BlockMassCounterexample.exact_counterexample
#print axioms BlockMassCounterexample.exact_operator_counterexample
#print axioms BlockMassCounterexample.not_universal_sum_claim
