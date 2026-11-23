import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow

noncomputable section

open NumberField Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE npow)
open scoped TensorProduct NNReal

namespace GlobalTheory.Published

def EisensteinMaximalParabolic : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    Algebra.Unramified (𝓞 F) (𝓞 E) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (j : ℕ) (hj : j ≤ r) (C : Matrix (Fin n) (Fin j) E), C = X.submatrix id (Fin.castLE hj) →
      ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), IsAdapted σ J X Y L a →
      ∀ h : GAd σ J → ℝ≥0,
        (∀ (p : GAd σ J) (b : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * b.1 →
          ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E (Matrix.GeneralLinearGroup.det b)) →
      ∀ φ : GAd σ J → ℂ, IsAutOn σ J (leftGrp σ J C fun _ => 0) (levelAll σ J L a) φ →
      ∃ (Eis : ℂ → GAd σ J → ℂ) (σ₀ : ℝ),
        (∀ s : ℂ, σ₀ < s.re → ∀ g,
          GlobalTheory.Eis.CosetConv (parFlag σ J C fun _ => 0) (ratPts σ J) (fun x => φ x * npow (h x) s) g ∧
          Eis s g = GlobalTheory.Eis.cosetSum (parFlag σ J C fun _ => 0) (ratPts σ J) (fun x => φ x * npow (h x) s) g) ∧
        ∀ s₀ : ℂ, ∃ (k : ℕ) (U : Set ℂ) (H : ℂ → GAd σ J → ℂ), U ∈ 𝓝 s₀ ∧
          (∀ s ∈ U, s ≠ s₀ → ∀ g, H s g = (s - s₀) ^ k * Eis s g) ∧ (∀ s ∈ U, IsSmoothModerate σ J (H s)) ∧
          ∀ μ, IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H s)) U

end GlobalTheory.Published

end
