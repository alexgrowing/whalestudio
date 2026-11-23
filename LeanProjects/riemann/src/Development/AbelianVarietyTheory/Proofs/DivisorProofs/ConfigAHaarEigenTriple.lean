import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactSupportSchwartzDecayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigATripleMatchedCompareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigATripleMatchedEqualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigATripleMatchedFoldStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.ConeTate

theorem integrable_cone_integrand : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ (μ : Measure (AE F E)ˣ), μ.IsHaarMeasure → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), ∀ y : Fin b × Fin (b + a') → AF F,
      Integrable (fun l : (AE F E)ˣ => e (G.M.co.rho B.ψ (shiftA H H' l) Φ) y * (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2)) μ := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC μ hμ e he X om om' om₁ om₁' hT hT₁ Φ hΦ y
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hcont := GlobalTheory.T.config_A_triple_matched_equal hKP F E σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ Φ hΦ y
  obtain ⟨K, hK, hsupp⟩ := GlobalTheory.T.config_A_triple_matched_compare hKP F E σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ Φ hΦ y _ (Module.finBasis F E)
  have hdec := GlobalTheory.T.config_A_triple_matched_fold hKP F E σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ Φ hΦ y _ (Module.finBasis F E)
  have hz : 2 ≤ (b + 2 - a') / 2 := by
    have h1 := hT.geo.eBig
    have h2 := hC.ep
    have h3 := hC.q0
    omega
  have hI := GlobalTheory.T.compact_support_schwartz_decay F E _ (Module.finBasis F E) _ hcont ⟨K, hK, hsupp⟩ hdec μ hμ _ hz
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  have hν : Continuous fun l : (AE F E)ˣ => (X.ν l : ℂ) := by
    have h : Continuous (⇑X.α / ⇑X.β) := hT.chars.heckeα.1.div' hT.chars.heckeβ.1
    have e1 : ⇑X.ν = ⇑X.α / ⇑X.β := rfl
    rw [← e1] at h
    exact continuous_subtype_val.comp h
  refine hI.mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    exact ((hcont.comp Units.continuous_val).mul hν).mul
      ((Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE)).pow _)
  · refine Filter.Eventually.of_forall fun l => ?_
    simp only [norm_mul, norm_pow, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs, NNReal.abs_eq]
    rfl

end GlobalTheory.ConeTate
