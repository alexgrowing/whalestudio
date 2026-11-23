import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeLeSpanInvariantVectors
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_degree_le_span_invariant_vectors : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (om : Rep σ X W) (χ₁ χ₂ : Chr F E) (r s r' s' : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M.IsWeil B.ψ χ₁ χ₂ om →
    ∀ k ∈ KInf σ W B.emb, ∀ j : ℕ, fockDeg M B.ψ B.emb j ≤ Submodule.span ℂ {f | f ∈ fockDeg M B.ψ B.emb j ∧
      ∃ c : ℂ, ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) (⇑f) (⇑f₁) → f₁ = c • f} := by
  first | exact @GlobalTheory.FockDiag.fockDeg_le_span_eigen | exact GlobalTheory.FockDiag.fockDeg_le_span_eigen | (intros; apply GlobalTheory.FockDiag.fockDeg_le_span_eigen <;> assumption)
