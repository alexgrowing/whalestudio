import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarAtOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLiftFormsFiniteGroupAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicLiftDatumOfConjugateLiftDatumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralTsumOfFactor
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace

open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.UnitCoefIP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem exists_scalar : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), (∀ χ ∈ A.X, IsAbsIrrChar χ) → GlobalTheory.LiftRows.SourceLevelLawC R F → GlobalTheory.LiftRows.InnerProductFormulaC R F → GlobalTheory.LiftRows.FockCoefficientC R F → GlobalTheory.LiftRows.FiniteZetaL R F → GlobalTheory.LiftRows.RealLowestKTypeCoeffSquareIntegrable R →
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (μ' η' : (AE D)ˣ →* Circle)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (c : CoefA (Vc D i))
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (H : HMod (Bridge.Gf (Vc D i) → c.W)),
  GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io →
  IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0) →
  Bridge.IsReps (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y →
  H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m))) (Bridge.adInner (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y) →
  ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, (∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) →
  ∀ ev : Pl D.host.E → List ℤ → ℂ, ∃ C : ℂ, ∀ y₁ ∈ GlobalTheory.LiftLower.partH R i σ ev, ∀ (y₂ : (R.HW i σ).H) (w : c.W), ‖w‖ = 1 →
    GlobalTheory.AdelicScalar.l2 (R.νV i A.μ0) (R.fdV i A.μ0) (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e y₁ fun ρ => v ρ)) (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e y₂ fun ρ => v ρ)) = C * inner ℂ y₁ y₂ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F _hirr _hS hI hFo hZ hδ i σ s m μ' η' ω B f₀ f c io H hd hν _hy _hH v hv ev
  have hC := hd.1
  obtain ⟨⟨μ, 𝓧⟩, hμ⟩ := hd.2.2.2.2.2.2.2.1.1.2.norm.1
  obtain ⟨⟨Fr, hFr⟩, hFr2⟩ := (hC.models.νW i).1.2.2 R.θ hC.models.inf
  obtain ⟨mR, hmR⟩ := (hFr2 Fr hFr).1
  choose δ _hδpos hδ' using hδ i σ
  have hδv : ∀ ρ, ∫ b, ‖⟪((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ),
      (R.MW i σ).rep ρ (realMat (Wc D i) Fr ρ b) ((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ‖ ^ 2 ∂(mR ρ) = δ ρ :=
    fun ρ => (hδ' ρ Fr hFr (mR ρ) (hmR ρ) (v ρ) (hv ρ)).2
  have hW := GlobalTheory.LiftScalarL.inner_HW R hC.models.HW i σ
  set N : ℝ := ∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℝ) with hN
  have hN0 : (N : ℂ) ≠ 0 := by
    have : 0 < N := Finset.prod_pos fun ρ _ => by
      have := one_le_dimK i σ ρ
      positivity
    exact_mod_cast this.ne'
  by_cases h0 : typePart R i σ A.μ0 R.triv ev = ⊥
  · refine ⟨0, fun y₁ hy₁ y₂ w _ => ?_⟩
    have e1 : y₁ = 0 := by
      rw [← GlobalTheory.LiftLower.typePart_base hC.lev, h0] at hy₁
      exact (Submodule.mem_bot ℂ).1 hy₁
    subst e1
    simp [l2, Lift.pet, upLift, petW]
  · obtain ⟨Bf, -, -, -, hK⟩ := hZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd μ 𝓧 hμ ev h0
    refine ⟨(((R.νV i A.μ0) (R.fdV i A.μ0)).toReal : ℂ) * (Formalism.E.fock (deltaAtEmb D i σ) (deltaAtEmb D i σ) * (∏ ρ, (δ ρ : ℂ)) *
      ((Nat.card R.triv.H : ℂ) * (Datum.nrm2 μ 𝓧 f : ℂ) *
        (GlobalTheory.LFun.LSD D (finS R A.μ0) Bf μ' ((1 + (D.R.t : ℂ)) / 2) / (dOff D (finS R A.μ0) : ℂ)))) / N,
      fun y₁ hy₁ y₂ w hw => ?_⟩
    have hm : ∀ x, (R.HW i σ).e x ∈ R.Wall i σ := HMod_mem (hC.models.HW i σ)
    have hw' : ⟪w, w⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hw]; simp
    have hy' : y₁ ∈ typePart R i σ A.μ0 R.triv ev := by
      rw [GlobalTheory.LiftLower.typePart_base hC.lev]; exact hy₁
    have hK1 := hK _ (Submodule.mem_comap.1 hy') _ (hm y₂)
    have hIP := isMultiplicityInner_of_model (R.HW i σ) hW y₁ y₂
    have key := GlobalTheory.LiftScalarL.l2_upwardLift R hI hFo hd hν hμ hFr hmR (hm y₁) (hm y₂) hIP _ hK1 v δ hδv w hw'
    refine key.trans ?_
    rw [hW y₁ y₂]
    field_simp

end GlobalTheory.UnitCoefIP

end
