import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaEighth
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistLeftVertexParabolicIsGood
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedDownwardThetaLiftIsSmoothAutomorphic
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCuspValueHasTypeAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistDownTypeLiftApproxSpan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaEighthStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.LiftTypeDn
theorem downward_theta_lift_hasKType : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * φ g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) → ∀ τ, IsTypeAt R.θ (G.P i).V τ ((G.P i).S τ) (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * φ g ∂(G.mP (i + 1)).ν) := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG i hi Φ hΦ φ hφ hint τ
  have hsig : (G.P i).V.SigOK := (hG.spaces.P i hi.le).sigOK
  have hgood := _root_.GlobalTheory.T.twist_leftVertex_parabolic_isGood hP D hS G₀ Pl0 T A Ks R G hRB hG i hi τ
  have haut := _root_.GlobalTheory.T.twisted_downward_theta_lift_isSmoothAutomorphic hL hP D hS G₀ Pl0 T A Ks R G hRB hG i hi Φ hΦ φ hφ hint
  have hval := _root_.GlobalTheory.T.twist_cusp_value_hasTypeAt hP R.θ (G.P i) τ hRB.inf hsig hgood
  refine GlobalTheory.T.automorphicForm_uniformLimit_discreteSeries_series R.θ (G.P i).V τ ((G.P i).S τ) _ hP.discreteSeriesUpqExists
    (GlobalTheory.Published.discreteSeriesHermitianUnique_iff.1 hP.discreteSeriesHermitianUnique) hP.harishChandraModules
    hP.casselmanWallach hRB.inf hsig hgood haut ?_
  refine hasTypeAt_of_approx R.θ (G.P i).V τ ((G.P i).S τ) _ fun C hC δ hδ => ?_
  obtain ⟨χ, hχ, hC'⟩ := _root_.GlobalTheory.T.twist_downType_lift_approx_span hL hP D hS G₀ Pl0 T A Ks R G hRB hG i hi Φ hΦ φ hφ hint C hC δ hδ
  refine ⟨χ, ?_, hC'⟩
  have hle : Submodule.span ℂ {f : GA D (G.P i).V → ℂ | ∃ F ∈ (G.P i).Cusp R.θ, ∃ w, f = F w} ≤
      GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.typeSub R.θ (G.P i).V τ ((G.P i).S τ) := by
    rw [Submodule.span_le]
    rintro f ⟨F, hF, w, rfl⟩
    exact hval F hF w
  exact hle hχ
end GlobalTheory.LiftTypeDn
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_downward_theta_lift_hasKType : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * φ g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) → ∀ τ, IsTypeAt R.θ (G.P i).V τ ((G.P i).S τ) (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * φ g ∂(G.mP (i + 1)).ν) := by
  first | exact @_root_.GlobalTheory.LiftTypeDn.downward_theta_lift_hasKType | exact _root_.GlobalTheory.LiftTypeDn.downward_theta_lift_hasKType | (intros; apply _root_.GlobalTheory.LiftTypeDn.downward_theta_lift_hasKType <;> assumption)
end
