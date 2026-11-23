import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedRealLineFirst
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdaptedFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemTensSpan
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_real_line_first : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d d₁ i₀ i₁ r s r₁ s₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁), B.IsGood σ → W.IsSkew σ B r s →
    W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (Rn Sn : ℕ) (r₀ : Fin Rn) (s₀ : Fin Sn) (C : InfinitePlace F → Matrix (Fin d) (Formalism.BasicNotions.TH.Ix Rn Sn) ℂ),
    (∀ w, GlobalTheory.RealLift.IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w)) →
    (∀ w, W.θ w * C w = C w * Formalism.BasicNotions.TH.Jm Rn Sn) → GlobalTheory.FockBridge.IsAdaptedFrame B H' C r₀ s₀ →
    ∀ k ∈ KInf σ W B.emb, (∀ w, (∀ i, ((mat k).map (piInf (B.emb w)) * C w) i (.inl r₀) = C w i (.inl r₀)) ∧
        ∀ i, ((mat k).map (piInf (B.emb w)) * C w) i (.inr s₀) = C w i (.inr s₀)) →
      ∃ k₁ ∈ KInf σ W₁ B.emb, IsLevi H' 1 k₁ k := by
  first | exact @GlobalTheory.KInfLevi.exists_kInf_isLevi_of_fix | exact GlobalTheory.KInfLevi.exists_kInf_isLevi_of_fix | (intros; apply GlobalTheory.KInfLevi.exists_kInf_isLevi_of_fix <;> assumption)
