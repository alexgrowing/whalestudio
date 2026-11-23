import Mathlib
import Lemmata.MiscLemmasB.Imports

open MeasureTheory Topology

namespace Formalism.IndefR.Eqv.G5

theorem fdom_exists_all {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] :
    ∃ s : Set G, MeasurableSet s ∧ ∀ μ : Measure G, IsFundamentalDomain Γ s μ := by
  first | exact Bl.SecondBlockLemmaC.goal1 .. | (apply Bl.SecondBlockLemmaC.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaC.goal1 <;> assumption)

end Formalism.IndefR.Eqv.G5
