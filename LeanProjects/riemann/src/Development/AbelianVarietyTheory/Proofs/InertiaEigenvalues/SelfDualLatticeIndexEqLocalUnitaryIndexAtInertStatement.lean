import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeIndexEqLocalUnitaryIndexAtInert
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDeltaPsi
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLatticeIndex_eq_localUnitaryIndex_at_inert : ∀ (D : D7) (W : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε → ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (σ : GlobalTheory.InertLoc.LP D P →+* GlobalTheory.InertLoc.LP D P) (π : AE D →+* GlobalTheory.InertLoc.LP D P) (β : GL (Fin W.rank) (GlobalTheory.InertLoc.LP D P)) (ι : Formalism.UG.UJ σ (1 : Matrix (Fin W.rank) (Fin W.rank) (GlobalTheory.InertLoc.LP D P)) →* GA D W), GlobalTheory.InertLoc.Chart (algebraMap (AF D.host.F) (AE D) ε) σ π → GlobalTheory.InertLoc.Frame W (algebraMap (AF D.host.F) (AE D) ε) σ π β → GlobalTheory.InertLoc.GrpChart W (algebraMap (AF D.host.F) (AE D) ε) σ π β ι → ∀ (g : Formalism.UG.UJ σ (1 : Matrix (Fin W.rank) (Fin W.rank) (GlobalTheory.InertLoc.LP D P))), latIndex W (ι g) = ((Submodule.span (P.adicCompletionIntegers D.host.E) (Set.range (Pi.basisFun (GlobalTheory.InertLoc.LP D P) (Fin W.rank)))).map (((g : GL (Fin W.rank) (GlobalTheory.InertLoc.LP D P)) : Matrix (Fin W.rank) (Fin W.rank) (GlobalTheory.InertLoc.LP D P)).mulVecLin.restrictScalars (P.adicCompletionIntegers D.host.E))).toAddSubgroup.relIndex (Submodule.span (P.adicCompletionIntegers D.host.E) (Set.range (Pi.basisFun (GlobalTheory.InertLoc.LP D P) (Fin W.rank)))).toAddSubgroup := by
  first | exact @GlobalTheory.InertLatIndex.latIndex_chart_eq | exact GlobalTheory.InertLatIndex.latIndex_chart_eq | (intros; apply GlobalTheory.InertLatIndex.latIndex_chart_eq <;> assumption)
