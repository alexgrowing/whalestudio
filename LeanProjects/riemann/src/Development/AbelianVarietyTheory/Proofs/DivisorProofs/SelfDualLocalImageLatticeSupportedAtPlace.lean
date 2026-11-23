import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqIntegralSpanGenerato

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.LatVac.DualLoc

variable {F : Type} [Field F] [NumberField F]

theorem form_smul_left {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux B κ) (u : AF F) (z γ : W) : B (u • z) γ = u * B z γ := by
  rw [co.form, co.form, map_smul]
  simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul, mul_sub]

theorem at_form {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux B κ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {z : W}
    (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z) (γ : W) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (B z γ) := by
  intro u hu
  rw [smul_eq_mul, ← form_smul_left co, hz u hu, co.form]
  simp

theorem evFin_form {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux B κ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (z γ : W) :
    evFin F v (B z γ) = (GlobalTheory.LatVac.locCo co v z).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2 -
      (GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v z).2 := by
  rw [co.form]
  simp only [dotProduct, map_sub, map_sum, map_mul]
  rfl

theorem psi_form {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux B κ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (ψ : AddChar (AF F) ℂ) {z : W}
    (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z) (γ : W) :
    ψ (B z γ) = GlobalTheory.LatVac.psiAt ψ v ((GlobalTheory.LatVac.locCo co v z).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2 -
      (GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v z).2) := by
  rw [GlobalTheory.VacIndic.psi_of_at ψ (at_form co v hz γ), ← evFin_form co v z γ]
  rfl

theorem map_selfDual : ∀ {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {W : Type} [AddCommGroup W]
    [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ)
    (Λ : AddSubgroup W), (∀ γ ∈ Λ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) γ) →
    (∀ z : W, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → (z ∈ Λ ↔ ∀ γ ∈ Λ, ψ (B z γ) = 1)) →
    ∀ w : (κ → Fv F v) × (κ → Fv F v), w ∈ Λ.map (GlobalTheory.LatVac.locCo co v) ↔
      ∀ l ∈ Λ.map (GlobalTheory.LatVac.locCo co v), GlobalTheory.LatVac.psiAt ψ v (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1 := by
  intro F _ _ v W _ _ B κ _ co ψ Λ hat hdual w
  constructor
  · rintro ⟨z, hz, rfl⟩ l ⟨γ, hγ, rfl⟩
    rw [← psi_form co v ψ (hat z hz) γ]
    exact (hdual z (hat z hz)).1 hz γ hγ
  · intro hw
    obtain ⟨p, hp⟩ : ∃ p : (κ → AF F) × (κ → AF F),
        p = (fun k => GlobalTheory.LatVac.liftV v (w.1 k), fun k => GlobalTheory.LatVac.liftV v (w.2 k)) := ⟨_, rfl⟩
    have hzat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (co.e.symm p) := by
      intro u hu
      have hp0 : u • p = 0 := by
        subst hp
        refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
        · exact GlobalTheory.LatVac.at_liftV v (w.1 k) u hu
        · exact GlobalTheory.LatVac.at_liftV v (w.2 k) u hu
      rw [← map_smul, hp0, map_zero]
    have hloc : GlobalTheory.LatVac.locCo co v (co.e.symm p) = w := by
      subst hp
      refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
      · show evFin F v ((co.e (co.e.symm _)).1 k) = w.1 k
        rw [LinearEquiv.apply_symm_apply]
        exact GlobalTheory.LatVac.evFin_liftV v (w.1 k)
      · show evFin F v ((co.e (co.e.symm _)).2 k) = w.2 k
        rw [LinearEquiv.apply_symm_apply]
        exact GlobalTheory.LatVac.evFin_liftV v (w.2 k)
    have hz : co.e.symm p ∈ Λ := (hdual _ hzat).2 fun γ hγ => by
      rw [psi_form co v ψ hzat γ, hloc]
      exact hw _ ⟨γ, hγ, rfl⟩
    exact ⟨_, hz, hloc⟩

end GlobalTheory.LatVac.DualLoc
