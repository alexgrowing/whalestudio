import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeStabilizerDoubleCosetsClassRestMass
import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_stabilizer_doubleCosets_classRest_mass : ∀ D : D7, DefClassRest D := by
  first | exact @GlobalTheory.ClassRestObj.defClassRest | exact GlobalTheory.ClassRestObj.defClassRest | (intros; apply GlobalTheory.ClassRestObj.defClassRest <;> assumption)
