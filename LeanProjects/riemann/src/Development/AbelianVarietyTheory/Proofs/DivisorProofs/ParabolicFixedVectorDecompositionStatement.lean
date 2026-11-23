import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicFixedVectorDecomposition
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_fixed_vector_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∀ p ∈ UAt σ G.V (evI F), mat p *ᵥ incV F H.x = incV F H.x →
      ∃ (n m : UA σ G.V.J) (g₀ : UA σ G₁.V.J), n ∈ unip σ G.V H ∧ n ∈ UAt σ G.V (evI F) ∧
        IsLevi (W₁ := G₁.V) H 1 g₀ m ∧ m ∈ UAt σ G.V (evI F) ∧ g₀ ∈ UAt σ G₁.V (evI F) ∧ p = n * m := by
  first | exact @GlobalTheory.StabDecInf.stab_decomp_inf | exact GlobalTheory.StabDecInf.stab_decomp_inf | (intros; apply GlobalTheory.StabDecInf.stab_decomp_inf <;> assumption)
