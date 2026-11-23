import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilCompactLineAction
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_compact_line_action : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ W B.emb, ∀ δ ∈ Lines σ W, ∃ ε ∈ Lines σ W, ∀ f ∈ M.Pol B.ψ B.emb,
      ∀ f₁ f₂ f₃ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₁ →
        ActsD (evI F) (fun t => om (1, δ (Multiplicative.ofAdd t))) f f₂ →
        Acts (evI F) (om (1, k)) f₂ f₃ → ActsD (evI F) (fun t => om (1, ε (Multiplicative.ofAdd t))) f₁ f₃ := by
  first | exact @GlobalTheory.AdCompactLine.actsD_conj | exact GlobalTheory.AdCompactLine.actsD_conj | (intros; apply GlobalTheory.AdCompactLine.actsD_conj <;> assumption)
