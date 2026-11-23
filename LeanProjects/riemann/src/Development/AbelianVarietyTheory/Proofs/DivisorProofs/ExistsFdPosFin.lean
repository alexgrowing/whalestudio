import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartFPlaceIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaHeisenbergCommutingThetaOperatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNhdsZeroPrincipalEqZero
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

noncomputable section

namespace GlobalTheory.ThetaSchurUnitF

open scoped TensorProduct Matrix in
open NumberField IsDedekindDomain in
open MeasureTheory in

theorem _root_.GlobalTheory.ThetaSchurUnitF.exists_fd_pos_fin {F E : Type} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
    {ψ : AddChar (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ℂ} (hψ : ∀ a, ‖ψ a‖ = 1) {f : _root_.Formalism.IndefR.DatumF.WOF F E nS nT → ℂ}
    (hf : _root_.Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ ψ f)
    {y : _root_.Formalism.IndefR.DatumF.WOF F E nS nT} (hy : f y ≠ 0) :
    ∃ (μ : Measure (_root_.Formalism.IndefR.DatumF.WOF F E nS nT)) (𝓕 : Set (_root_.Formalism.IndefR.DatumF.WOF F E nS nT)), μ.IsAddHaarMeasure ∧
      IsAddFundamentalDomain (_root_.Formalism.IndefR.DatumF.ratLF F E nS nT) 𝓕 μ ∧
      (∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) ≠ 0 ∧ (∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) ≠ ⊤ := by
  obtain ⟨h1, h2, h3, h4, h5, K, hK, hcov⟩ := _root_.GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  haveI : BorelSpace (_root_.Formalism.IndefR.DatumF.WOF F E nS nT) := ⟨rfl⟩
  obtain ⟨⟨μ, 𝓕, hμ, h𝓕, -⟩, hN⟩ :=
    _root_.GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact _ (_root_.Formalism.IndefR.DatumF.ratLF F E nS nT) K hK hcov
  have hper : ∀ γ ∈ _root_.Formalism.IndefR.DatumF.ratLF F E nS nT, ∀ w, ‖f (γ + w)‖ = ‖f w‖ := by
    intro γ hγ w
    have h := _root_.GlobalTheory.ThetaSchurF.prod_periodic hψ hf hf hγ w
    simp only [← starRingEnd_apply, RCLike.mul_conj] at h
    have h' : ‖f (γ + w)‖ ^ 2 = ‖f w‖ ^ 2 := by exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h'
  obtain ⟨N, hN⟩ := hN f hf.cont hper
  obtain ⟨-, htop, hl, -⟩ := hN μ 𝓕 hμ h𝓕
  haveI : Countable (_root_.Formalism.IndefR.DatumF.ratLF F E nS nT) :=
    (TopologicalSpace.separableSpace_iff_countable).1 inferInstance
  refine ⟨μ, 𝓕, hμ, h𝓕, ?_, ?_⟩
  · intro hz
    have hall : ∫⁻ w, ‖f w‖ₑ ^ 2 ∂μ = 0 := by
      rw [h𝓕.lintegral_eq_tsum']
      refine ENNReal.tsum_eq_zero.2 fun γ => ?_
      rw [← hz]
      refine lintegral_congr fun w => ?_
      rw [AddSubgroup.vadd_def, vadd_eq_add, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
        hper _ (-γ).2 w]
    have hcont : Continuous fun w => ‖f w‖ₑ ^ 2 :=
      (ENNReal.continuous_pow 2).comp (continuous_enorm.comp hf.cont)
    have hae := (lintegral_eq_zero_iff hcont.measurable).1 hall
    have heq := (Continuous.ae_eq_iff_eq μ hcont continuous_const).1 hae
    have hfy := congrFun heq y
    simp [hy] at hfy
  · rw [hl]
    exact ENNReal.mul_ne_top htop (by simp)

end GlobalTheory.ThetaSchurUnitF

theorem GlobalTheory.ThetaSchurUnitF.main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ A A' : Module.End ℂ (WOF F E nS nT → ℂ),
        (∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ (A f)) →
        (∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ (A' f)) →
        (∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → A (A' f) = f) → (∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → A' (A f) = f) →
        (∀ (μ : MeasureTheory.Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
          MeasureTheory.IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
            ∫⁻ w in 𝓕, ‖A f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) →
        (∀ w₀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → A (heisOF σ JS JT ξ₀ B.ψ w₀ f) = heisOF σ JS JT ξ₀ B.ψ w₀ (A f)) →
        ∃ c : Circle, ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → A f = (c : ℂ) • f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ A A' hA _ _ _ hiso hcomm
  obtain ⟨c, hc⟩ := GlobalTheory.T.schur_lemma_heisenberg_commuting_thetaOperator F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ A hA hcomm hiso
  have hψ : ∀ a, ‖B.ψ a‖ = 1 := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB).1.2.1
  by_cases h0 : ∃ f y, IsThetaFunOF σ JS JT ξ₀ B.ψ f ∧ f y ≠ 0
  · obtain ⟨f, y, hf, hy⟩ := h0
    obtain ⟨μ, 𝓕, hμ, h𝓕, hI0, hIt⟩ := GlobalTheory.ThetaSchurUnitF.exists_fd_pos_fin hψ hf hy
    have h := hiso μ 𝓕 hμ h𝓕 f hf
    rw [hc f hf] at h
    simp only [Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow] at h
    rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top enorm_ne_top)] at h
    have h1 : ‖c‖ₑ ^ 2 = 1 := by
      have := congrArg (· / ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) h
      rwa [ENNReal.mul_div_cancel_right hI0 hIt, ENNReal.div_self hI0 hIt] at this
    have h2 : (‖c‖₊ : ENNReal) ^ 2 = 1 := by rwa [enorm_eq_nnnorm] at h1
    have h3 : ‖c‖₊ ^ 2 = 1 := by exact_mod_cast h2
    have h4 : ‖c‖ ^ 2 = 1 := by
      have := congrArg (fun t : NNReal => (t : ℝ)) h3
      simpa using this
    have hn : ‖c‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg c) two_ne_zero).1 h4
    exact ⟨⟨c, mem_sphere_zero_iff_norm.2 hn⟩, fun g hg => hc g hg⟩
  · push_neg at h0
    refine ⟨1, fun f hf => ?_⟩
    have : f = 0 := funext fun y => h0 f y hf
    subst this
    simp
