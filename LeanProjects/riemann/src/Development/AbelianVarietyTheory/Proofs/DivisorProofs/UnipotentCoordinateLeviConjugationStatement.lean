import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCoordinateLeviConjugation
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemImLine

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_coordinate_levi_conjugation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∀ (l : (AE F E)ˣ) (g₀ : UA σ G₁.V.J) (h : UA σ G.V.J), IsLevi H l g₀ h → ∀ n : UA σ G.V.J,
    GlobalTheory.ThK.UnipDom.coA σ G.V.J H (h * n * h⁻¹) = l.1 • ((mat g₀⁻¹)ᵀ *ᵥ GlobalTheory.ThK.UnipDom.coA σ G.V.J H n) ∧
    GlobalTheory.ThK.UnipDom.coC σ G.V.J H (h * n * h⁻¹) = l.1 * cA σ l.1 * GlobalTheory.ThK.UnipDom.coC σ G.V.J H n := by
  first | exact @GlobalTheory.ThK.UnipDom.LeviCoord.coA_coC_levi_conj | exact GlobalTheory.ThK.UnipDom.LeviCoord.coA_coC_levi_conj | (intros; apply GlobalTheory.ThK.UnipDom.LeviCoord.coA_coC_levi_conj <;> assumption)
