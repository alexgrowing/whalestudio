import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDefiniteSelfDualOfBaseFramePosDef
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDefiniteSelfDual_of_baseFrame_posDef : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), V.SigOK → V.IsPosDef → IsBaseFrame V β Λ N → IsDefUnimod D.sp.cm V.gram Λ := by
  first | exact @GlobalTheory.BaseFrameUnimod.isDefUnimod_of_isBaseFrame | exact GlobalTheory.BaseFrameUnimod.isDefUnimod_of_isBaseFrame | (intros; apply GlobalTheory.BaseFrameUnimod.isDefUnimod_of_isBaseFrame <;> assumption)
