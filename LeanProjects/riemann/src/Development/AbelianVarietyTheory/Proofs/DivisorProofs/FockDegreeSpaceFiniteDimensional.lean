import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergLineDerivativeFiniteSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianSpanFiniteDimensionalStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.FockDegFin

theorem span_actsD_finiteDimensional {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (N : Submodule ℂ (SInf F (Fin n × Fin d))) [FiniteDimensional ℂ N] :
    FiniteDimensional ℂ (Submodule.span ℂ {f₁ : SInf F (Fin n × Fin d) |
      ∃ u, At (evI F) u ∧ ∃ f ∈ N, ActsD (evI F) (M.heisLine ψ u) f f₁}) := by
  obtain ⟨m, L, hL⟩ := GlobalTheory.HeisDerivSpan.heisLine_deriv_finite_span F E σ n d X W M ψ hψ
  have hle : Submodule.span ℂ {f₁ : SInf F (Fin n × Fin d) |
      ∃ u, At (evI F) u ∧ ∃ f ∈ N, ActsD (evI F) (M.heisLine ψ u) f f₁} ≤ ⨆ i, N.map (L i) := by
    refine Submodule.span_le.2 ?_
    rintro f₁ ⟨u, hu, f, hf, hd⟩
    obtain ⟨D, hD, hDs⟩ := hL u hu
    rw [(hD f f₁).1 hd]
    refine Submodule.span_le.2 ?_ (hDs f)
    rintro _ ⟨i, rfl⟩
    exact Submodule.mem_iSup_of_mem i ⟨f, hf, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

theorem fockDeg_finiteDimensional : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ j : ℕ, FiniteDimensional ℂ (fockDeg M B.ψ B.emb j) := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW hM j
  induction j with
  | zero => rw [fockDeg_zero]; exact GlobalTheory.T.gaussian_span_finite_dimensional F E σ B n d X W M r s r' s' hB hX hW hM
  | succ k ih =>
    rw [fockDeg_succ]
    haveI := ih
    haveI := span_actsD_finiteDimensional M B.ψ hB.std (fockDeg M B.ψ B.emb k)
    infer_instance

end GlobalTheory.FockDegFin
