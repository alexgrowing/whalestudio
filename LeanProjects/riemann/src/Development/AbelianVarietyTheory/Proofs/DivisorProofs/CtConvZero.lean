import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ConvCT

set_option synthInstance.maxHeartbeats 200000 in

theorem ct_conv_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d d₁ : ℕ}
    (W : Spc F E d) (H' : Plane E d d₁) (μ : Measure (UA σ W.J)), μ.IsHaarMeasure →
    ∀ f φ : UA σ W.J → ℂ, Continuous f → (∃ C : ℝ, ∀ h, ‖f h‖ ≤ C) → Integrable φ μ → IsCT H' f 0 →
      IsCT H' (fun h => ∫ g, φ g * f (h * g) ∂μ) 0 := by
  intro F E _ _ _ _ _ σ d d₁ W H' μ hμ f φ hf hb hφ hct
  obtain ⟨C, hC⟩ := hb
  obtain ⟨hTG, hLC, hSC, hT2⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ d W.J
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  haveI : SigmaCompactSpace (UA σ W.J) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI hsf : SigmaFinite μ := inferInstance
  haveI : SFinite μ := by first | exact instSFiniteOfSigmaFinite | infer_instance
  intro ν 𝓕 hν hfd h𝓕 h
  haveI hfin : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h𝓕]; simp⟩
  haveI : SFinite (ν.restrict 𝓕) := inferInstance
  have hinner : ∀ g, ∫ u in 𝓕, φ g * f (u.1 * h * g) ∂ν = 0 := by
    intro g
    rw [integral_const_mul]
    have := hct ν 𝓕 hν hfd h𝓕 (h * g)
    simp only [Pi.zero_apply] at this
    simp only [mul_assoc, ← this, mul_zero]
  have hcont : Continuous fun p : unip σ W H' × UA σ W.J => f (p.1.1 * h * p.2) := by
    fun_prop
  have hint : Integrable (Function.uncurry fun (u : unip σ W H') (g : UA σ W.J) => φ g * f (u.1 * h * g))
      ((ν.restrict 𝓕).prod μ) := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).mul_prod (hφ.norm.const_mul C)) ?_ ?_
    · have h1 : AEStronglyMeasurable (fun p : unip σ W H' × UA σ W.J => φ p.2) ((ν.restrict 𝓕).prod μ) :=
        hφ.aestronglyMeasurable.comp_snd
      exact h1.mul hcont.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun p => ?_
      obtain ⟨u, g⟩ := p
      simp only [Function.uncurry_apply_pair, norm_mul, one_mul]
      rw [mul_comm C]
      exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  simp only [Pi.zero_apply]
  rw [integral_integral_swap hint]
  simp [hinner]

end GlobalTheory.ConvCT
