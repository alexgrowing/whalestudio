import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingPairStabiliserIntegral
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxC
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer
open GlobalTheory.DblDatum
open GlobalTheory.DblDatum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubling_pair_stabiliser_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (Xs : Spc F E n) (W : Spc F E d) (M : Model σ Xs W) (χX χW : Chr F E) (om : Rep σ Xs W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ →
    ∀ W₂ : Spc F E (d + d), W₂.J = dblGram finSumFinEquiv W.J → W₂.L = sumLat finSumFinEquiv W.L W.L →
    ∀ K₂ : Subgroup (UA σ W₂.J), IsStab B K₂ → ∀ N ∈ 𝓝 (1 : UA σ W₂.J),
      ∃ s : Finset (UA σ W₂.J), (∀ k ∈ s, k ∈ K₂ ∧ k ∈ UAt σ W₂ (sndA F)) ∧
        ∀ f ∈ K₂, f ∈ UAt σ W₂ (sndA F) → ∃ k ∈ s, k⁻¹ * f ∈ N ∧ k⁻¹ * f ∈ UAt σ W₂ (sndA F) := by
  first | exact @GlobalTheory.DblKFinCpt.finite_cover | exact GlobalTheory.DblKFinCpt.finite_cover | (intros; apply GlobalTheory.DblKFinCpt.finite_cover <;> assumption)
