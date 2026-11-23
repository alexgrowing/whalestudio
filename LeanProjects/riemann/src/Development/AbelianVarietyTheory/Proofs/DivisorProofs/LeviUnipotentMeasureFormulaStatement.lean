import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviUnipotentMeasureFormula
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_unipotent_measure_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∀ m : (AE F E)ˣ → UA σ G₁.V.J → UA σ G.V.J, (∀ l g₀, IsLevi H l g₀ (m l g₀)) →
    ∀ μN : Measure (unip σ G.V H), μN.IsHaarMeasure →
    ∀ γ ∈ ratU σ G₁.V.J, ∀ f : UA σ G.V.J → ENNReal, Measurable f →
      ∫⁻ n, f (n.1 * m 1 γ) ∂μN = ∫⁻ n, f (m 1 γ * n.1) ∂μN := by
  first | exact @GlobalTheory.LeviConjHaar.lintegral_conj_levi | exact GlobalTheory.LeviConjHaar.lintegral_conj_levi | (intros; apply GlobalTheory.LeviConjHaar.lintegral_conj_levi <;> assumption)
