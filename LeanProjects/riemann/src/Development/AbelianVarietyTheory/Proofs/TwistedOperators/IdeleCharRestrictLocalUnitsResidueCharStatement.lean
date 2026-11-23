import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdeleCharRestrictLocalUnitsResidueChar
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnrOffOne
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideleChar_restrict_localUnits_residueChar : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → ∀ PP : Pl D.host.E, (∀ a : (kP PP)ˣ →* ℂˣ, χ.TameAt PP → IsRes χ PP a → GlobalTheory.StepLaw.ResAt c PP a) ∧ (χ.UnrAt PP → GlobalTheory.StepLaw.ResAt c PP 1) := by
  first | exact @GlobalTheory.ResLoc.resAt_of_chrEq | exact GlobalTheory.ResLoc.resAt_of_chrEq | (intros; apply GlobalTheory.ResLoc.resAt_of_chrEq <;> assumption)
