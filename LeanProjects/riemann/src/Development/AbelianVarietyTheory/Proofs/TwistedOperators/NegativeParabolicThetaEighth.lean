import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaSixthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodParameterDiagonalNodesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormHasTypeOfGoodParameterStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSetSumApproximationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.LiftTypeDn

theorem hasTypeAt_of_approx {D : D7} (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (S : SPar) (ψ : GA D V → ℂ)
    (h : ∀ C : Set (GA D V), IsCompact C → ∀ δ : ℝ, 0 < δ →
      ∃ χ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ V τ S χ ∧ ∀ x ∈ C, ‖ψ x - χ x‖ < δ) :
    GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ V τ S ψ := by
  intro C hC δ hδ
  obtain ⟨χ, hχ, h1⟩ := h C hC (δ / 2) (by linarith)
  obtain ⟨ψ', hψ', h2⟩ := hχ C hC (δ / 2) (by linarith)
  refine ⟨ψ', hψ', fun x hx => ?_⟩
  have e : ψ x - ψ' x = (ψ x - χ x) + (χ x - ψ' x) := by ring
  rw [e]
  have := norm_add_le (ψ x - χ x) (χ x - ψ' x)
  linarith [h1 x hx, h2 x hx]

theorem isTypeAt_lift_down : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * φ g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) → ∀ τ, IsTypeAt R.θ (G.P i).V τ ((G.P i).S τ) (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * φ g ∂(G.mP (i + 1)).ν) := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG i hi Φ hΦ φ hφ hint τ
  have hsig : (G.P i).V.SigOK := (hG.spaces.P i hi.le).sigOK
  have hgood := GlobalTheory.T.good_parameter_diagonal_nodes hP D hS G₀ Pl0 T A Ks R G hRB hG i hi τ
  have haut := GlobalTheory.T.negative_parabolic_theta_sixth hL hP D hS G₀ Pl0 T A Ks R G hRB hG i hi Φ hΦ φ hφ hint
  have hval := GlobalTheory.T.cusp_form_has_type_of_good_parameter hP R.θ (G.P i) τ hRB.inf hsig hgood
  refine GlobalTheory.T.automorphicForm_uniformLimit_discreteSeries_series R.θ (G.P i).V τ ((G.P i).S τ) _ hP.discreteSeriesUpqExists
    (GlobalTheory.Published.discreteSeriesHermitianUnique_iff.1 hP.discreteSeriesHermitianUnique) hP.harishChandraModules
    hP.casselmanWallach hRB.inf hsig hgood haut ?_
  refine hasTypeAt_of_approx R.θ (G.P i).V τ ((G.P i).S τ) _ fun C hC δ hδ => ?_
  obtain ⟨χ, hχ, hC'⟩ := GlobalTheory.T.theta_lift_diagonal_level_preserved hL hP D hS G₀ Pl0 T A Ks R G hRB hG i hi Φ hΦ φ hφ hint C hC δ hδ
  refine ⟨χ, ?_, hC'⟩
  have hle : Submodule.span ℂ {f : GA D (G.P i).V → ℂ | ∃ F ∈ (G.P i).Cusp R.θ, ∃ w, f = F w} ≤
      GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.typeSub R.θ (G.P i).V τ ((G.P i).S τ) := by
    rw [Submodule.span_le]
    rintro f ⟨F, hF, w, rfl⟩
    exact hval F hF w
  exact hle hχ

end GlobalTheory.LiftTypeDn
