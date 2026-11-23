import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilLineCommutatorAction
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_line_commutator_action : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ κ ∈ Lines σ W, ∀ δ ∈ Lines σ W, ∃ ε ∈ Lines σ W, ∀ f ∈ M.Pol B.ψ B.emb,
      ∀ f₁ f₂ f₁₂ f₂₁ g : SInf F (Fin n × Fin d),
        ActsD (evI F) (fun t => om (1, κ (Multiplicative.ofAdd t))) f f₁ →
        ActsD (evI F) (fun t => om (1, δ (Multiplicative.ofAdd t))) f f₂ →
        ActsD (evI F) (fun t => om (1, δ (Multiplicative.ofAdd t))) f₁ f₁₂ →
        ActsD (evI F) (fun t => om (1, κ (Multiplicative.ofAdd t))) f₂ f₂₁ →
        ActsD (evI F) (fun t => om (1, ε (Multiplicative.ofAdd t))) f g → f₂₁ - f₁₂ = g := by
  first | exact @GlobalTheory.LineBracket.exists_line_bracket | exact GlobalTheory.LineBracket.exists_line_bracket | (intros; apply GlobalTheory.LineBracket.exists_line_bracket <;> assumption)
