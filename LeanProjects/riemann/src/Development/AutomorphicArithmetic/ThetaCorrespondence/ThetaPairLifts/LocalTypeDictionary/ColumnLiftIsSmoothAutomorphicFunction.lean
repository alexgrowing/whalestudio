import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VerticalThetaLevelSecond
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistDeformationLiftSmooth
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DefiniteUnitaryLiftFiniteAdeles
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistLiftModerateGrowth
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WeilRepresentationLevelEqConductor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VerticalThetaLevelSecondStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
open scoped ContDiff ComplexOrder
namespace GlobalTheory.ColLiftAut
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {Φ : WO S T → ℂ}
theorem thetaLift_isAutomorphicFunction (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hW : IsWeilDatumO ψ S T χS χT om) (hΦ : IsThetaFunO ψ S T Φ)
    (hS : ∀ τ, (gramAt D S τ).PosDef) {ν : Measure (GA D S)} {𝓕 : Set (GA D S)} (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ S) 𝓕 ν) {φ : GA D S → ℂ} (hφ : IsAutFun S φ) :
    IsAutFun T fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν := by
  refine ⟨fun γ hγ h => ?_, ?_, lift_continuous hW hΦ hS hν h𝓕 hφ⟩
  · simp only [kernel_left hW hΦ _ hγ]
  · obtain ⟨U, hU, hk⟩ := _root_.GlobalTheory.T.twist_weil_level_eq_conductor ψ S T χS χT om Φ hP hW hΦ
    refine ⟨U, hU, fun k hkU hkf h => ?_⟩
    simp only [kernel_right, hk k hkU hkf]
theorem thetaLift_isSmoothAutomorphicFunction (θ : InfFam D) (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ)
    (hΦ : IsThetaFunO ψ S T Φ) (hS : ∀ τ, (gramAt D S τ).PosDef) (hT : ∀ τ, (gramAt D T τ).PosDef)
    {ν : Measure (GA D S)} {𝓕 : Set (GA D S)} (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ S) 𝓕 ν)
    {φ : GA D S → ℂ} (hφ : IsAutFunSm θ S φ) :
    IsAutFunSm θ T fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν :=
  { toIsAutFun := _root_.GlobalTheory.ColLiftAut.thetaLift_isAutomorphicFunction hP hW hΦ hS hν h𝓕 hφ.toIsAutFun
    smooth := _root_.GlobalTheory.T.twist_deformation_lift_smooth ψ θ S T χS χT om Φ φ ν 𝓕 hP hW hθ hΦ hS hT hν h𝓕 hφ
    zfin := _root_.GlobalTheory.T.twist_definite_lift_finite_adeles ψ θ S T χS χT om Φ φ ν 𝓕 hP hW hθ hΦ hS hT hν h𝓕 hφ
    growth := _root_.GlobalTheory.T.twist_lift_moderate_growth ψ θ S T χS χT om Φ φ ν 𝓕 hP hW hθ hΦ hS hT hν h𝓕 hφ }
end GlobalTheory.ColLiftAut
namespace GlobalTheory.ColLiftAut
theorem columnLift_isSmoothAutomorphicFunction : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.Xp j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.col t j).ω g h Φ * φ g) (G.measX j).fd (G.measX j).ν) → IsAutFunSm R.θ (G.Xp (j + 1)).V (fun h => ∫ g in (G.measX j).fd, thetaKO (G.col t j).ω g h Φ * φ g ∂(G.measX j).ν) := by
  intro _ hPr D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t j hj Φ hΦ φ hφ _
  have hW : IsWeilDatumO R.ψ (G.Xp j).V (G.Xp (j + 1)).V (R.toLevCh.mu t (j + 1)) (R.toLevCh.mu t (j + 1)) (G.col t j).ω :=
    (hG.arrows.col t j hj).weil
  have hT : ∀ τ, (gramAt D (G.Xp (j + 1)).V τ).PosDef := posDef_of_nodeIs (hG.spaces.X j (by omega)) rfl
  have hSm : (∀ τ, (gramAt D (G.Xp j).V τ).PosDef) ∧ (G.measX j).ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ (G.Xp j).V) (G.measX j).fd (G.measX j).ν := by
    cases j with
    | zero =>
      exact ⟨posDef_of_nodeIs (hG.spaces.P D.R.m le_rfl) (by simp), ((hG.meas.P D.R.m le_rfl).1 rfl).1.1, ((hG.meas.P D.R.m le_rfl).1 rfl).2⟩
    | succ j' =>
      exact ⟨posDef_of_nodeIs (hG.spaces.X j' (by omega)) rfl, ((hG.meas.X j' (by omega)).1 trivial).1.1, ((hG.meas.X j' (by omega)).1 trivial).2⟩
  exact _root_.GlobalTheory.ColLiftAut.thetaLift_isSmoothAutomorphicFunction R.θ hPr hW hRB.inf hΦ hSm.1 hT hSm.2.1 hSm.2.2 hφ.1
end GlobalTheory.ColLiftAut
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnLift_isAutomorphicFunction : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.Xp j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.col t j).ω g h Φ * φ g) (G.measX j).fd (G.measX j).ν) → IsAutFunSm R.θ (G.Xp (j + 1)).V (fun h => ∫ g in (G.measX j).fd, thetaKO (G.col t j).ω g h Φ * φ g ∂(G.measX j).ν) := by
  first | exact @_root_.GlobalTheory.ColLiftAut.columnLift_isSmoothAutomorphicFunction | exact _root_.GlobalTheory.ColLiftAut.columnLift_isSmoothAutomorphicFunction | (intros; apply _root_.GlobalTheory.ColLiftAut.columnLift_isSmoothAutomorphicFunction <;> assumption)
end
