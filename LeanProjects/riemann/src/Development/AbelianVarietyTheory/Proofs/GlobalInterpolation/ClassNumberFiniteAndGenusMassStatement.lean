import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassNumberFiniteAndGenusMass
import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classNumber_finite_and_genusMass : ∀ D : D7, ClassFin D ∧ ClassMass D := by
  first | exact @GlobalTheory.ClassNumberMass.classFin_and_classMass | exact GlobalTheory.ClassNumberMass.classFin_and_classMass | (intros; apply GlobalTheory.ClassNumberMass.classFin_and_classMass <;> assumption)
