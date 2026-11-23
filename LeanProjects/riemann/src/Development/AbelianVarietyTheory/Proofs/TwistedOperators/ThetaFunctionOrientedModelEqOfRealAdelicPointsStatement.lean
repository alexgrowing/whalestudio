import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionOrientedModelEqOfRealAdelicPoints
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaAtEqProdAhG
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunction_orientedModel_eq_of_realAdelicPoints : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (f₁ f₂ : WO S T → ℂ),
    IsThetaFunO ψ S T f₁ → IsThetaFunO ψ S T f₂ →
    (∀ X : Matrix (Fin T.rank) (Fin S.rank) D.host.E, f₁ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T X) = f₂ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T X)) →
    f₁ = f₂ := by
  first | exact @GlobalTheory.ThetaUniqReal.eq_of_eq_realPt | exact GlobalTheory.ThetaUniqReal.eq_of_eq_realPt | (intros; apply GlobalTheory.ThetaUniqReal.eq_of_eq_realPt <;> assumption)
