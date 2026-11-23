import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatricesDiscreteCocompactAdelicMatrixSpa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfNorms
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars

noncomputable section

open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

namespace GlobalTheory.RealWeilF

theorem lintegral_rhoBF {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
    {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT))
    (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ) (u : WOF F E nS nT)
    (G : BBF σ JS JT ξ₀ ψ) :
    ∫⁻ w in 𝓕, ‖(rhoBF σ JS JT ξ₀ ψ hψ u G).1 w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖G.1 w‖ₑ ^ 2 ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hc⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hfin := GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hc μ h𝓕
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  have key : ∀ H : BBF σ JS JT ξ₀ ψ, ∫⁻ w in 𝓕, ‖H.1 w‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ w in 𝓕, ‖H.1 w‖ ^ 2 ∂μ) := by
    intro H
    rw [ofReal_integral_eq_lintegral_ofReal _ (Filter.Eventually.of_forall fun w => by positivity)]
    · simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    · exact Integrable.of_bound (H.1.continuous.norm.pow 2).aestronglyMeasurable (‖H‖ ^ 2)
        (Filter.Eventually.of_forall fun w => by
          rw [norm_pow, norm_norm]; exact pow_le_pow_left₀ (norm_nonneg _) (norm_ev_le w H) 2)
  rw [key, key, coe_rhoBF]
  simp only [norm_heisOF hψ]
  rw [GlobalTheory.HeisOrtho.setIntegral_add_right (G := WOF F E nS nT) (ratLF F E nS nT) μ 𝓕 h𝓕 (fun w => ‖G.1 w‖ ^ 2)
    (fun γ hγ w => by rw [BBF_norm_periodic hψ G γ hγ]) u]

theorem lintegral_eq_of_normsF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ψ : AddChar (AF F) ℂ)
    (hψ : IsCharAF F ψ), ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ f f' : BBF σ JS JT ξ₀ ψ,
      (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Φ : BBF σ JS JT ξ₀ ψ →L[ℂ] H),
        (∀ w g, ‖Φ (rhoBF σ JS JT ξ₀ ψ hψ w g)‖ = ‖Φ g‖) → ‖Φ f'‖ = ‖Φ f‖) →
      ∫⁻ w in 𝓕, ‖f'.1 w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f.1 w‖ₑ ^ 2 ∂μ := by
  intro F E _ _ _ _ _ σ nS nT JS JT ξ₀ ψ hψ μ 𝓕 hμ h𝓕 f f' hn
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hc⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hlt := GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hc μ h𝓕
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  rw [lintegral_norm_sq_eq_toL2, lintegral_norm_sq_eq_toL2, enorm_sq_inj]
  refine hn _ (toL2 _ _ (μ.restrict 𝓕)) fun v G => ?_
  rw [← enorm_sq_inj, ← lintegral_norm_sq_eq_toL2, ← lintegral_norm_sq_eq_toL2]
  exact lintegral_rhoBF hψ μ 𝓕 hμ h𝓕 _ G

end GlobalTheory.RealWeilF

end
