import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFormulaOfKernel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeterssonIntegralFormulaStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InnerProductIntegralFormulaStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointPairingUnfoldingDownwardLiftStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UpwardVectorLiftMemRangeCoefficientExtensionStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.AdjUp

namespace GlobalTheory.AdjUp

set_option maxHeartbeats 1000000 in

theorem adjFormula_holds : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, AdjFormula R i t := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t th hth v hv n b
  refine (GlobalTheory.T.petersson_integral_formula hP D G Pl0 T A Ks R F hL i v hv).elim fun P hPx => ?_
  refine (GlobalTheory.T.inner_product_integral_formula D G Pl0 T A Ks R F hL i t).elim fun c hcx => ?_
  have hval : ∀ u, val R i v (th u) = R.thF i t u (fun ρ => v ρ) := fun u => by
    show (R.HW i (sg0 D A)).e (th u) (fun ρ => v ρ) = _
    rw [hth u]
  have hK0 : ∀ k h, upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v 0) h = 0 := fun k h => by
    rw [val_zero]; exact upLift_zero _ _ _ _ h
  exact adjoint_formula_of_kernel th b ((R.νW i).restrict (R.fdW i)) ((R.νV i t).restrict (R.fdV i t)) (val R i v)
    (fun u => R.thF i t u (fun ρ => v ρ)) (R.extV i t)
    (fun k y h => upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v y) h) P c hPx.1 hcx.1 hPx.2
    hval (val_zero R i v) hK0 hcx.2 (fun y u => GlobalTheory.T.adjoint_pairing_unfolding_downward_lift hP D G Pl0 T A Ks R F hL hF i t v n b y u)
    (fun y => GlobalTheory.T.upwardVectorLift_mem_range_coefficientExtension hP D G Pl0 T A Ks R F hL hF i t v n b y)

end GlobalTheory.AdjUp
