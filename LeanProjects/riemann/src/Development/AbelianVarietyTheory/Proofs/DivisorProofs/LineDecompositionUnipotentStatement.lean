import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDecompositionUnipotent
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_decomposition_unipotent : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ γ ∈ Lines σ W, ∃ γu ∈ Lines σ W, ∃ γl ∈ Lines σ W, ∃ γk ∈ Lines σ W, (∀ t, γu t ∈ unip σ W H') ∧
      (∃ (τ : Multiplicative ℝ →* (AE F E)ˣ) (γ₁ : Multiplicative ℝ →* UA σ W₁.J), γ₁ ∈ Lines σ W₁ ∧
        ∀ t, IsLevi H' (τ t) (γ₁ t) (γl t)) ∧ (∀ t, γk t ∈ KInf σ W B.emb) ∧
      ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ g₁ g₂ g₃ : SInf F (Fin n × Fin d),
        ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
        ActsD (evI F) (fun t => om (1, γu (Multiplicative.ofAdd t))) f g₁ →
        ActsD (evI F) (fun t => om (1, γl (Multiplicative.ofAdd t))) f g₂ →
        ActsD (evI F) (fun t => om (1, γk (Multiplicative.ofAdd t))) f g₃ → f₁ = g₁ + g₂ + g₃ := by
  first | exact @GlobalTheory.IndLine.Iwasawa.line_decomposition | exact GlobalTheory.IndLine.Iwasawa.line_decomposition | (intros; apply GlobalTheory.IndLine.Iwasawa.line_decomposition <;> assumption)
