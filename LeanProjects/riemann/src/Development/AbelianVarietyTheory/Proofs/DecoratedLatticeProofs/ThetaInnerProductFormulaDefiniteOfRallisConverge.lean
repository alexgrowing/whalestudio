import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftPairPositiveDefiniteWittIndexZeroCartanStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaDatumFockVectorsAreFockVectorsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralUnitaryAdelicEqSumFiniteCosetsRealIntegrStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeterssonPrincipalLevelContinuousRightInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousWeilCoefficientFockVectorsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalLevelFixesFockVectorsFiniteDatumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IPFConv

theorem integrableOn_of_quot {D : D7} {V : HSp D} {μ : Measure (GA D V)} [μ.IsMulLeftInvariant]
    {𝓕 : Set (GA D V)} (hFD : IsFundamentalDomain (GQ V) 𝓕 μ) {φ : GA D V → ℂ}
    (hφ : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) φ)
    (h : Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) φ) (GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) μ)) : IntegrableOn φ 𝓕 μ := by
  have h1 := (GlobalTheory.AutomorphicL2Unitary.memLp_quotMeasure_iff hFD).1 (memLp_one_iff_integrable.2 h)
  rw [hφ.lift_descend] at h1
  exact memLp_one_iff_integrable.1 h1

theorem thetaKO_left_snd {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hω : IsWeilDatumO ψ V W χV χW ω)
    {φ : WO V W → ℂ} (hf : IsThetaFunO ψ V W φ) (h : GA D V) :
    GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ W) (fun g => thetaKO ω h g φ) := fun γ hγ g => by
  have e : ((h, γ * g) : GA D V × GA D W) = (1, γ) * (h, g) := by simp
  show thetaKO ω h (γ * g) φ = thetaKO ω h g φ
  unfold thetaKO
  rw [e, map_mul]
  exact hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ φ hf)

theorem innerProductFormulaC_of_convergent : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.Convergent D → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → InnerProductFormulaC R F := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F hConv hpar
  intro i t σ s P cμ cη m ω BW f₀ f c io hL
  intro ν 𝓕 hν μ 𝓧 hμ Fr hFr mR hmR U₁ hU₁ U₂ hU₂ v₁ v₂ Q₁ Q₂
  intro φ₁ φ₂ F₁ F₂ Z pt
  have hCore : GlobalTheory.Hk3.Core R F := hL.1
  have hω : IsWeilDatumO R.ψ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω := hL.2.2.2.2.2.1
  obtain ⟨hwitt, hrank, cA, hSet, hA0⟩ := GlobalTheory.T.liftPair_positiveDefinite_wittIndexZero_cartan R F hCore hpar i σ
  have hFo₁ := GlobalTheory.T.thetaDatum_fockVectors_areFockVectors R F i t σ s P cμ cη m ω BW f₀ f c io hL Q₁
  have hFo₂ := GlobalTheory.T.thetaDatum_fockVectors_areFockVectors R F i t σ s P cμ cη m ω BW f₀ f c io hL Q₂
  have hW := hCore.models.νW i
  haveI : (R.νW i).IsHaarMeasure := hW.1.1
  have hFDW : IsFundamentalDomain (GQ (Wc D i)) (R.fdW i) (R.νW i) := hW.2
  haveI : ν.IsHaarMeasure := hν.1.1
  have hFDV : IsFundamentalDomain (GQ (Vc D i)) 𝓕 ν := hν.2
  have hF₁ : F₁ ∈ GlobalTheory.Cusp.A0 R.θ (Wc D i) cA := hA0 U₁ hU₁ v₁
  have hF₂ : F₂ ∈ GlobalTheory.Cusp.A0 R.θ (Wc D i) cA := hA0 U₂ hU₂ v₂
  have hL₁ : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (Wc D i)) F₁ := (Submodule.mem_inf.1 hF₁).2.2.1
  have hL₂ : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (Wc D i)) F₂ := (Submodule.mem_inf.1 hF₂).2.2.1
  have hKP : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsKernelPair R.ψ R.θ (Wc D i) (Vc D i) (cμ * cη⁻¹) cμ (cart (R.MW i σ)) (fun _ => 1)
      true (fun _ => True) (fun _ => True) (fun g h => thetaKO ω h g φ₁) (fun g h => thetaKO ω h g φ₂)
      (fun g => l2 μ 𝓧 (ω (1, g) φ₁) φ₂) :=
    ⟨ω, φ₁, φ₂, hω, hFo₁, hFo₂, trivial, trivial, fun _ _ => rfl, fun _ _ => rfl, μ, 𝓧, hμ, fun _ => rfl⟩
  obtain ⟨hC₁, hC₂, hInt, hEq⟩ := hConv R.ψ R.θ (Wc D i) (Vc D i) (cμ * cη⁻¹) cμ (cart (R.MW i σ)) (fun _ => 1) D.R.t
    cA true (fun g h => thetaKO ω h g φ₁) (fun g h => thetaKO ω h g φ₂) (fun g => l2 μ 𝓧 (ω (1, g) φ₁) φ₂)
    (R.νW i) ν F₁ F₂ hSet (Or.inl hwitt) hrank hKP inferInstance inferInstance hF₁ hF₂
  have hpetW : ∀ u₁ u₂ : GA D (Wc D i) → ℂ, GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (Wc D i)) u₁ →
      GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (Wc D i)) u₂ → GlobalTheory.Cusp.petersson (Wc D i) (R.νW i) u₁ u₂ = petW R i u₁ u₂ :=
    fun u₁ u₂ h₁ h₂ => GlobalTheory.AutomorphicL2Unitary.pet_eq hFDW h₁ h₂
  have hlift₁ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift (R.νW i) (fun g h => thetaKO ω h g φ₁) F₁ = upLift R i ω φ₁ F₁ :=
    funext fun h => hpetW _ _ (thetaKO_left_snd hω hFo₁.1 h) hL₁
  have hlift₂ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift (R.νW i) (fun g h => thetaKO ω h g φ₂) F₂ = upLift R i ω φ₂ F₂ :=
    funext fun h => hpetW _ _ (thetaKO_left_snd hω hFo₂.1 h) hL₂
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.LiftConv at hC₁ hC₂
  rw [hlift₁] at hC₁ hEq
  rw [hlift₂] at hC₂ hEq
  have hZeq : ∀ g, l2 μ 𝓧 (ω (1, g) φ₁) φ₂ *
      conj (GlobalTheory.Cusp.petersson (Wc D i) (R.νW i) (rTr (Wc D i) g F₁) F₂) = Z g := fun g => by
    rw [hpetW (rTr (Wc D i) g F₁) F₂ (hL₁.mul_right g) hL₂]
  have hpc := GlobalTheory.T.petersson_principal_level_continuous_right_invariant hP R F hCore i σ
  have hZc : Continuous Z :=
    (GlobalTheory.T.continuous_weilCoefficient_fockVectors R F i t σ s P cμ cη m ω BW f₀ f c io hL μ 𝓧 hμ Q₁ Q₂).mul
      (Complex.continuous_conj.comp (hpc.2 U₁ hU₁ U₂ hU₂ _ _).1)
  have hZi : Integrable Z (R.νW i) := hInt.congr (ae_of_all _ hZeq)
  have hZr : ∀ g, ∀ k ∈ levW R i, Z (g * k) = Z g := fun g k hk => by
    have hk1 := GlobalTheory.T.principalLevel_fixes_fockVectors_finiteDatum R F i t σ s P cμ cη m ω BW f₀ f c io hL Q₁ k hk
    have e : (((1 : GA D (Vc D i)), g * k) : GA D (Vc D i) × GA D (Wc D i)) = (1, g) * (1, k) := by simp
    show l2 μ 𝓧 (ω (1, g * k) φ₁) φ₂ * starRingEnd ℂ (petW R i (rTr (Wc D i) (g * k) F₁) F₂) =
      l2 μ 𝓧 (ω (1, g) φ₁) φ₂ * starRingEnd ℂ (petW R i (rTr (Wc D i) g F₁) F₂)
    rw [e, map_mul, Module.End.mul_apply, hk1, (hpc.2 U₁ hU₁ U₂ hU₂ _ _).2 g k hk]
  obtain ⟨hfin, hdis⟩ := GlobalTheory.T.integral_unitaryAdelic_eq_sum_finiteCosets_realIntegrals D R.θ hSet.2.2.2.1 (Wc D i) hSet.2.2.2.2.1 _ (R.νW i) hW.1 hpc.1 Fr hFr mR
    hmR Z hZc hZi hZr
  refine ⟨fun h => ?_, ?_, hfin, ?_⟩
  · have hLp : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (Wc D i)) (fun g => thetaKO ω h g φ₁ * starRingEnd ℂ (F₁ g)) :=
      fun γ hγ g => by
        have e1 : thetaKO ω h (γ * g) φ₁ = thetaKO ω h g φ₁ := thetaKO_left_snd hω hFo₁.1 h γ hγ g
        have e2 : F₁ (γ * g) = F₁ g := hL₁ γ hγ g
        show thetaKO ω h (γ * g) φ₁ * starRingEnd ℂ (F₁ (γ * g)) = _
        rw [e1, e2]
    exact integrableOn_of_quot hFDW hLp (hC₁.1 h)
  · have hLp : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (Vc D i))
        (fun h => upLift R i ω φ₁ F₁ h * starRingEnd ℂ (upLift R i ω φ₂ F₂ h)) := fun γ hγ g => by
      have e1 : upLift R i ω φ₁ F₁ (γ * g) = upLift R i ω φ₁ F₁ g := hC₁.2.1 γ hγ g
      have e2 : upLift R i ω φ₂ F₂ (γ * g) = upLift R i ω φ₂ F₂ g := hC₂.2.1 γ hγ g
      show upLift R i ω φ₁ F₁ (γ * g) * starRingEnd ℂ (upLift R i ω φ₂ F₂ (γ * g)) = _
      rw [e1, e2]
    exact integrableOn_of_quot hFDV hLp (hC₁.2.integrable_mul_conj hC₂.2)
  · have hvol : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ (Vc D i) ν = (ν 𝓕).toReal := by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ, GlobalTheory.AutomorphicL2Unitary.autMeasure, Measure.real, GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hFDV]
    have hpV : GlobalTheory.Cusp.petersson (Vc D i) ν (upLift R i ω φ₁ F₁) (upLift R i ω φ₂ F₂) =
        l2 ν 𝓕 (upLift R i ω φ₁ F₁) (upLift R i ω φ₂ F₂) := GlobalTheory.AutomorphicL2Unitary.pet_eq hFDV hC₁.2.1 hC₂.2.1
    have hI : ∫ g, l2 μ 𝓧 (ω (1, g) φ₁) φ₂ *
        conj (GlobalTheory.Cusp.petersson (Wc D i) (R.νW i) (rTr (Wc D i) g F₁) F₂) ∂(R.νW i) = ∫ g, Z g ∂(R.νW i) :=
      integral_congr_ae (ae_of_all _ hZeq)
    rw [hpV, hvol, hI, hdis] at hEq
    exact hEq

end GlobalTheory.IPFConv
