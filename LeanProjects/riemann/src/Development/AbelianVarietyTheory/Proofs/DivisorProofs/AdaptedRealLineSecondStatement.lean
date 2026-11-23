import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedRealLineSecond
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
theorem _root_.GlobalTheory.T.adapted_real_line_second : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d d₁ i₀ i₁ r s r₁ s₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁), B.IsGood σ → W.IsSkew σ B r s →
    W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (Rn Sn : ℕ) (r₀ : Fin Rn) (s₀ : Fin Sn) (C : InfinitePlace F → Matrix (Fin d) (Formalism.BasicNotions.TH.Ix Rn Sn) ℂ),
    (∀ w, GlobalTheory.RealLift.IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w)) →
    (∀ w, W.θ w * C w = C w * Formalism.BasicNotions.TH.Jm Rn Sn) → GlobalTheory.FockBridge.IsAdaptedFrame B H' C r₀ s₀ →
    ∀ k ∈ KInf σ W B.emb, ∀ t : (AE F E)ˣ, IsLevi H' t (1 : UA σ W₁.J) k →
      At (evI F) ((t : AE F E) - 1) ∧ (absE F E t : ℝ) = 1 ∧ ∀ w, ‖piInf (B.emb w) (t : AE F E)‖ = 1 ∧
        (∀ i, ((mat k).map (piInf (B.emb w)) * C w) i (.inl r₀) = piInf (B.emb w) (t : AE F E) * C w i (.inl r₀)) ∧
        (∀ i, ((mat k).map (piInf (B.emb w)) * C w) i (.inr s₀) = piInf (B.emb w) (t : AE F E) * C w i (.inr s₀)) ∧
        ∀ c, c ≠ .inl r₀ → c ≠ .inr s₀ → ∀ i, ((mat k).map (piInf (B.emb w)) * C w) i c = C w i c := by
  first | exact @GlobalTheory.LeviKCentre.levi_one_kInf | exact GlobalTheory.LeviKCentre.levi_one_kInf | (intros; apply GlobalTheory.LeviKCentre.levi_one_kInf <;> assumption)
