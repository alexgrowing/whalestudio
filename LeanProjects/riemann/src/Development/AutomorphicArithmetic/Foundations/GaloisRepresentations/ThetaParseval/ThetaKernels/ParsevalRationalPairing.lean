import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ParsevalAdelicPairFundamental
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsStdCharFOfIsGoodK

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.ParsevalPolarization
open GlobalTheory.ThetaTransform
theorem parseval_rational_pairing : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E}, _root_.UpperTheory.TP.W.GoodK σ B → ∀ (N : ℕ),
    letI : MeasurableSpace (Fin N → AF F) := borel _
    letI : MeasurableSpace (VA F N) := borel _
    ∀ (ν : Measure (VA F N)), ν.IsAddHaarMeasure → ∀ 𝓕 : Set (VA F N),
      IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N)) 𝓕 ν →
      ∃ (μ : Measure (Fin N → AF F)) (c : ℝ), μ.IsAddHaarMeasure ∧ 0 < c ∧
        ∀ Φ₁ ∈ schA F (Fin N), ∀ Φ₂ ∈ schA F (Fin N),
          ∫ w in 𝓕, thV B.ψ Φ₁ w * starRingEnd ℂ (thV B.ψ Φ₂ w) ∂ν =
            (c : ℂ) * ∫ x, Φ₁ x * starRingEnd ℂ (Φ₂ x) ∂μ := by
  intro F E _ _ _ _ _ σ B hB N
  letI mA : MeasurableSpace (Fin N → AF F) := borel _
  letI mV : MeasurableSpace (VA F N) := borel _
  intro ν hν 𝓕 h𝓕
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : BorelSpace (Fin N → AF F) := ⟨rfl⟩
  have hR : IsTotallyReal F := hB.cm.1
  have hψ : IsCharAF F B.ψ := (_root_.GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B hB).1
  let μ : Measure (Fin N → AF F) := Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  obtain ⟨𝓕₁, h𝓕₁, h0, htop⟩ := GlobalTheory.T.exists_fundDomain_rationalPointsAdeleTuple_finite_pos F (Fin N) μ hμ
  obtain ⟨c₁, hc0, hctop, hc⟩ := GlobalTheory.T.lintegral_rationalPair_fundDomain_eq_iterated F (Fin N) μ hμ ν hν 𝓕 h𝓕 𝓕₁ h𝓕₁
  set K : ENNReal := c₁ * μ 𝓕₁ with hK
  have hK0 : K ≠ 0 := mul_ne_zero hc0 h0
  have hKt : K ≠ ⊤ := ENNReal.mul_ne_top hctop htop
  have hpar : ∀ Φ ∈ schA F (Fin N), ∫⁻ w in 𝓕, ‖thV B.ψ Φ w‖ₑ ^ 2 ∂ν = K * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
    intro Φ hΦ
    have hm := GlobalTheory.T.measurable_theta_sum_of_schrodinger F B.ψ hψ (Fin N) Φ hΦ
    have hG : @Measurable _ _ (borel _) _ (fun w : (Fin N → AF F) × (Fin N → AF F) =>
        ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr B.ψ w Φ)‖ₑ ^ 2) := Measurable.pow_const (measurable_enorm.comp hm) 2
    show ∫⁻ w in 𝓕, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr B.ψ w Φ)‖ₑ ^ 2 ∂ν = _
    rw [hc _ hG (fun γ hγ w => by
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, GlobalTheory.T.norm_adelicThetaSum_schroedinger_rationalPair_invariant F B.ψ hψ (Fin N) Φ γ hγ w])]
    simp_rw [GlobalTheory.T.lintegral_adelicThetaSum_sq_parseval_second_variable F B.ψ hψ (Fin N) μ hμ 𝓕₁ h𝓕₁ htop Φ hΦ]
    rw [lintegral_const_mul' _ _ htop, GlobalTheory.T.parseval_fundamental_domain_theta F (Fin N) μ hμ 𝓕₁ h𝓕₁ Φ hΦ, hK, mul_assoc]
  have henorm : ∀ z : ℂ, ‖‖z‖ ^ 2‖ₑ = ‖z‖ₑ ^ 2 := fun z => by
    rw [Real.enorm_eq_ofReal (by positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have hΦint : ∀ Φ ∈ schA F (Fin N), Integrable (fun x => ‖Φ x‖ ^ 2) μ := fun Φ hΦ =>
    (GlobalTheory.WeilM.schA_memLp_two F (Fin N) μ hμ Φ hΦ).integrable_norm_pow two_ne_zero
  have hthint : ∀ Φ ∈ schA F (Fin N), Integrable (fun w => ‖thV B.ψ Φ w‖ ^ 2) (ν.restrict 𝓕) := by
    intro Φ hΦ
    have hm := GlobalTheory.T.measurable_theta_sum_of_schrodinger F B.ψ hψ (Fin N) Φ hΦ
    refine ⟨((hm.norm.pow_const 2).aestronglyMeasurable), ?_⟩
    show ∫⁻ w in 𝓕, ‖‖thV B.ψ Φ w‖ ^ 2‖ₑ ∂ν < ⊤
    simp_rw [henorm]
    rw [hpar Φ hΦ]
    refine ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hKt) ?_
    have := (hΦint Φ hΦ).2
    unfold HasFiniteIntegral at this
    simp_rw [henorm] at this
    exact this
  have hreal : ∀ Φ ∈ schA F (Fin N), ∫ w in 𝓕, ‖thV B.ψ Φ w‖ ^ 2 ∂ν = K.toReal * ∫ x, ‖Φ x‖ ^ 2 ∂μ := by
    intro Φ hΦ
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _)
        (hthint Φ hΦ).aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _) (hΦint Φ hΦ).aestronglyMeasurable]
    have e1 : ∀ z : ℂ, ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ 2 := fun z => by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    simp_rw [e1]
    rw [hpar Φ hΦ, ENNReal.toReal_mul]
  refine ⟨μ, K.toReal, hμ, ENNReal.toReal_pos hK0 hKt, fun Φ₁ hΦ₁ Φ₂ hΦ₂ => ?_⟩
  have hmem : ∀ a : ℂ, Φ₁ + a • Φ₂ ∈ schA F (Fin N) := fun a => add_mem hΦ₁ (Submodule.smul_mem _ a hΦ₂)
  have hth : ∀ a : ℂ, thV B.ψ (Φ₁ + a • Φ₂) = fun w => thV B.ψ Φ₁ w + a * thV B.ψ Φ₂ w := by
    intro a
    rw [thV_add hR hψ (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ₁ hΦ₁) (GlobalTheory.SchwartzDecay.decay_smul a (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ₂ hΦ₂)),
      thV_smul]
    rfl
  have hfn : ∀ a : ℂ, (Φ₁ + a • Φ₂) = fun x => Φ₁ x + a * Φ₂ x := fun a => rfl
  refine polar μ (ν.restrict 𝓕) Φ₁ Φ₂ (thV B.ψ Φ₁) (thV B.ψ Φ₂) K.toReal (fun a => ?_) (fun a => ?_) (fun a => ?_)
  · have := hΦint _ (hmem a)
    rwa [hfn a] at this
  · have := hthint _ (hmem a)
    rwa [hth a] at this
  · have := hreal _ (hmem a)
    rwa [hth a, hfn a] at this
end PositivityTheory.ThKW.ParsevalPolarization
end
end
