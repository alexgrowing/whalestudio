import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionTheoryAnisotropicCompactQuotient
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompReixMemAdm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.DblBox
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_theory_anisotropic_compact_quotient : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    (∀ (n r s' : ℕ) (X : Spc F E n), X.IsHerm σ B r s' → min r s' = 0 →
      ∃ C : Set (UA σ X.J), IsCompact C ∧ ∀ g, ∃ γ ∈ ratU σ X.J, ∃ c ∈ C, g = γ * c) ∧
    ∀ (d r₁ s₁ : ℕ) (W : Spc F E d), W.IsSkew σ B r₁ s₁ → min r₁ s₁ = 0 → (∀ x, form σ W.J x x = 0 → x = 0) ∧
      ∃ C : Set (UA σ W.J), IsCompact C ∧ ∀ h, ∃ γ ∈ ratU σ W.J, ∃ c ∈ C, h = γ * c := by
  first | exact @GlobalTheory.ThK.DefCocompact.cocompact_of_definite | exact GlobalTheory.ThK.DefCocompact.cocompact_of_definite | (intros; apply GlobalTheory.ThK.DefCocompact.cocompact_of_definite <;> assumption)
