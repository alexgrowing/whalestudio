import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemTranslate
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDoubleLiftAdditive
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsDoubleLiftPeriodValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslateSobolevSepContinuous
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupQuotientFundamentalDomainCocompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawWeilBiActionCommutes
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepLinearRelationsPeriods
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawCommonRealDatumBiThetaVacuumContraction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedDataEqKernelDataAtLevel
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsJointlySmoothBiThetaTwoVarCombinationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TriStep.Lin

open GlobalTheory.Core.Mi.SepPer

variable {D : D7}

theorem per_int {ρ : ℕ} (B : BesLev D ρ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {φ : GA D B.A → ℂ} (hφ : IsContAut B.A φ) {f : GA D B.V → ℂ} (hf : f ∈ contLeft B.V) :
    (∀ h, IntegrableOn (GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h) B.vN.𝓝 B.vN.ν) ∧
      IntegrableOn (fun h => ∫ n in B.vN.𝓝, GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν) B.vA.𝓕 B.vA.μ := by
  obtain ⟨-, -, ⟨Ω, hΩc, hΩ⟩, -⟩ := GlobalTheory.T.besselGroup_quotient_fundamentalDomain_cocompact D ρ B
  obtain ⟨Cφ, hCφ⟩ := GlobalTheory.Unf.EvalCont.bounded_of_contAut B.cpt hφ
  have hμ : B.vA.μ B.vA.𝓕 < ⊤ := GlobalTheory.Unf.vol_fund_lt_top B.cpt B.vA
  have hν1 : B.vN.ν B.vN.𝓝 = 1 := B.vN.unit.2.2
  have hν : B.vN.ν B.vN.𝓝 < ⊤ := by rw [hν1]; exact ENNReal.one_lt_top
  haveI : IsFiniteMeasure (B.vN.ν.restrict B.vN.𝓝) := isFiniteMeasure_restrict.2 hν.ne
  have hemb := GlobalTheory.Unf.BesSemi.continuous_embA B.d B.o
  have hpsi := GlobalTheory.CharLaws.continuous_psiBes ψ B.d hψ.1.1 1 (vecB B.o B.ζ)
  obtain ⟨K, hK⟩ := hΩc.exists_bound_of_continuousOn hf.1.continuousOn
  have hsup : ∀ (h : GA D B.A) (n : flagN B.d), ‖f (n.1 * embA B.d B.o h)‖ ≤ K := by
    intro h n
    have hs : n.1 * embA B.d B.o h ∈ besGrp B.d B.o :=
      mul_mem (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right ⟨h, rfl⟩)
    obtain ⟨γ, hγ, hγs⟩ := hΩ _ hs
    rw [← hf.2 γ (Subgroup.mem_inf.1 hγ).1]
    exact hK _ hγs
  have hbd : ∀ h n, ‖GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n‖ ≤ Cφ * K := by
    intro h n
    simp only [GlobalTheory.MixPer.besFun, norm_mul, norm_star, norm_psiBes hψ, mul_one]
    exact mul_le_mul (hCφ h) (hsup h n) (norm_nonneg _) ((norm_nonneg _).trans (hCφ h))
  have hcont : ∀ h, Continuous (GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h) := by
    intro h
    change Continuous fun n : flagN B.d => φ h * f (n.1 * embA B.d B.o h) * star (psiBes ψ B.d 1 (vecB B.o B.ζ) n.1)
    exact (continuous_const.mul (hf.1.comp (continuous_subtype_val.mul continuous_const))).mul
      (continuous_star.comp (hpsi.comp continuous_subtype_val))
  have hcontH : ∀ n : flagN B.d, Continuous fun h => GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n := by
    intro n
    simp only [GlobalTheory.MixPer.besFun]
    exact (hφ.2.mul (hf.1.comp (continuous_const.mul hemb))).mul continuous_const
  have houtC : Continuous fun h => ∫ n in B.vN.𝓝, GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν := by
    haveI := GlobalTheory.Unf.EvalCont.firstCountable_GA B.A
    exact continuous_of_dominated (bound := fun _ => Cφ * K)
      (fun h => (hcont h).aestronglyMeasurable)
      (fun h => Filter.Eventually.of_forall fun n => hbd h n) (integrable_const _)
      (Filter.Eventually.of_forall fun n => hcontH n)
  refine ⟨fun h => Measure.integrableOn_of_bounded hν.ne (hcont h).aestronglyMeasurable
    (Filter.Eventually.of_forall fun n => hbd h n), ?_⟩
  refine Measure.integrableOn_of_bounded (M := Cφ * K * B.vN.ν.real B.vN.𝓝) hμ.ne houtC.aestronglyMeasurable
    (Filter.Eventually.of_forall fun h => ?_)
  exact norm_setIntegral_le_of_norm_le_const hν fun n _ => hbd h n

theorem per_add_left {ρ : ℕ} (B : BesLev D ρ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {φ₁ φ₂ : GA D B.A → ℂ} (h₁ : IsContAut B.A φ₁) (h₂ : IsContAut B.A φ₂) {f : GA D B.V → ℂ} (hf : f ∈ contLeft B.V) :
    B.per ψ (φ₁ + φ₂) f = B.per ψ φ₁ f + B.per ψ φ₂ f := by
  obtain ⟨i₁, o₁⟩ := per_int B hψ h₁ hf
  obtain ⟨i₂, o₂⟩ := per_int B hψ h₂ hf
  have e : ∀ h n, GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ (φ₁ + φ₂) f h n =
      GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ₁ f h n + GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ₂ f h n := by
    intro h n; simp only [GlobalTheory.MixPer.besFun, Pi.add_apply]; ring
  simp only [GlobalTheory.Unf.BesLev.per, GlobalTheory.MixPer.besPer]
  simp_rw [e]
  rw [← integral_add o₁ o₂]
  exact integral_congr_ae (Filter.Eventually.of_forall fun h => integral_add (i₁ h) (i₂ h))

theorem biComb_add (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ)
    (K K' : WO A S → WO S A' → ℂ) : biComb ψ A S A' c c' (K + K') = biComb ψ A S A' c c' K + biComb ψ A S A' c c' K' := by
  funext u v
  simp only [biComb, GlobalTheory.FrComb.comb_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem biComb_smul (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ)
    (a : ℂ) (K : WO A S → WO S A' → ℂ) : biComb ψ A S A' c c' (a • K) = a • biComb ψ A S A' c c' K := by
  funext u v
  simp only [biComb, GlobalTheory.FrComb.comb_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

end GlobalTheory.TriStep.Lin

open GlobalTheory.TriStep.Lin GlobalTheory.Core.Mi.SepPer in

theorem GlobalTheory.TriStep.valK_bilin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → (∀ Ξ, IsBiTheta ψ S.B.A S.J.W₀ S.B'.A (Λ Ξ)) → ∃ T : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] GlobalTheory.TriStep.space Q →ₗ[ℂ] ℂ, ∀ Ξ f, T Ξ f = GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ Ξ f.1 := by
  intro D ψ hψ σ S Q c₁ c₂ _ _ φ hφ Λ _ hΛ
  have hB : BiAct D := GlobalTheory.SeeSaw.biAct_all D
  have hC : ∀ Ξ, IsBiTheta ψ S.B.A S.J.W₀ S.B'.A (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ Ξ)) :=
    fun Ξ => GlobalTheory.T.isJointlySmoothBiTheta_twoVarCombination D ψ hψ S.B.A S.J.W₀ S.B'.A (Λ Ξ) (hΛ Ξ) c₁ c₂
  have hA : ∀ Ξ, IsContAut S.B'.A (biLift S.oma S.omb S.B.vA S.J.v0 φ (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ Ξ))) :=
    fun Ξ => GlobalTheory.SeeSawLastValue.contAut_biLift hB S.weila S.weilb S.B.cpt S.J.cpt S.B.vA S.J.v0 hφ (hC Ξ)
  have hL : ∀ Ξ Ξ', biLift S.oma S.omb S.B.vA S.J.v0 φ (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (Ξ + Ξ'))) =
      biLift S.oma S.omb S.B.vA S.J.v0 φ (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ Ξ)) +
        biLift S.oma S.omb S.B.vA S.J.v0 φ (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ Ξ')) := by
    intro Ξ Ξ'
    funext h₂
    have e := GlobalTheory.SeeSmallPf.biLift_sum hB S.weila S.weilb S.B.cpt S.J.cpt S.B.vA S.J.v0 hφ
      ![biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ Ξ), biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ Ξ')]
      (fun i => by fin_cases i <;> simp [hC]) h₂
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at e
    rw [map_add, biComb_add, e, Pi.add_apply]
  have hf : ∀ f : GlobalTheory.TriStep.space Q, f.1 ∈ contLeft S.B'.V := by
    intro f
    have := f.2.1 1
    rw [map_one, GlobalTheory.TriStep.rTrans_one] at this
    exact ⟨this.2, this.1⟩
  refine ⟨LinearMap.mk₂ ℂ (fun Ξ f => GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ Ξ f.1) ?_ ?_ ?_ ?_, fun Ξ f => rfl⟩
  · intro Ξ Ξ' f
    simp only [GlobalTheory.TriStep.valK]
    rw [hL, per_add_left S.B' hψ (hA Ξ) (hA Ξ') (hf f)]
  · intro a Ξ f
    simp only [GlobalTheory.TriStep.valK]
    rw [map_smul, biComb_smul, GlobalTheory.SeeSawRhs.biLift_smul, GlobalTheory.SeeSawStep.per_smul_left, smul_eq_mul]
  · intro Ξ f g
    simp only [GlobalTheory.TriStep.valK]
    obtain ⟨-, -, ⟨Ω, hΩc, hΩ⟩, -⟩ := GlobalTheory.T.besselGroup_quotient_fundamentalDomain_cocompact D σ S.B'
    obtain ⟨Cp, hadd, -⟩ := per_add_bound S.B' hψ (hA Ξ) Ω hΩc hΩ
    exact hadd _ _ (hf f) (hf g)
  · intro a Ξ f
    simp only [GlobalTheory.TriStep.valK]
    exact GlobalTheory.SeeSawStep.per_smul_right S.B' ψ _ a f.1
