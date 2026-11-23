import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosedSubgroupOfLocalStabilizerPairs
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDetInt
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closedSubgroup_of_localStabilizerPairs : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (H : Subgroup (GA D S × GA D T)), IsClosed (H : Set (GA D S × GA D T)) → (∀ v ε, IsPlaceIdem D v ε → ∀ g h, Stab S βS g → Stab T βT h → SuppPl ε S g → SuppPl ε T h → (g, h) ∈ H) → ∀ g h, Stab S βS g → Stab T βT h → (g, h) ∈ H := by
  first | exact @GlobalTheory.StabDense.mem_of_local | exact GlobalTheory.StabDense.mem_of_local | (intros; apply GlobalTheory.StabDense.mem_of_local <;> assumption)
