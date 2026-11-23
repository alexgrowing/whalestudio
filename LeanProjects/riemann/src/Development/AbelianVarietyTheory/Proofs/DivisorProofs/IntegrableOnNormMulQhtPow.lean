import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTopSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerRestrictsToOrthocomp
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.RapidInteg

theorem integrableOn_norm_mul_qht_pow : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) {d : ℕ}
    (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (μ : Measure (UA σ W.J)) (𝓕 : Set (UA σ W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) 𝓕 μ →
    ∀ f : UA σ W.J → ℂ, Continuous f → (∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C) →
      ∀ N : ℕ, IntegrableOn (fun h => ‖f h‖ * (qht h : ℝ) ^ N) 𝓕 μ := by
  intro hK F E _ _ _ _ _ σ B d W r s hB hW μ 𝓕 hμ hD f hf hdec N
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hB.cm
  obtain ⟨c, hc, hcs⟩ := GlobalTheory.CMImag.exists_imag_ne_zero F E σ hB.cm
  have hd : W.J.det ≠ 0 := GlobalTheory.IsoPlaneProj.det_ne_zero_of_cartan B W hW.cartan
  have hH : IsHermND σ (c • W.J.map σ) := GlobalTheory.ThKOrthVInt.isHermND_smul_of_skew hσ hW.skew hd hc hcs
  have hfin : μ 𝓕 < ⊤ := GlobalTheory.ThKOrthVInt.measure_fundDom_lt_top_smul hK.siegelSetUnitary hB.cm hc hH hD
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.UnitaryVol.countable_ratU σ W.J
  have hht : ∀ γ : ratU σ W.J, Measurable (fun h : UA σ W.J => ht (γ.1 * h)) := fun γ =>
    ((GlobalTheory.Grow.continuous_heightGL F).comp (continuous_subtype_val.comp (continuous_const.mul continuous_id))).measurable
  have hq : Measurable (fun h : UA σ W.J => qht h) := Measurable.iInf hht
  have hmeas : Measurable (fun h => ‖f h‖ * (qht h : ℝ) ^ N) :=
    hf.norm.measurable.mul ((measurable_coe_nnreal_real.comp hq).pow_const N)
  obtain ⟨C, hC⟩ := hdec N
  refine Measure.integrableOn_of_bounded hfin.ne hmeas.aestronglyMeasurable (M := C) (Eventually.of_forall fun h => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg (NNReal.coe_nonneg _) _))]
  exact hC h

end GlobalTheory.RapidInteg

end
