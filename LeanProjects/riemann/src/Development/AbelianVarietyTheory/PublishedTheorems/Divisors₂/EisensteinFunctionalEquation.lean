import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic

noncomputable section

open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE npow)
open scoped TensorProduct NNReal

namespace GlobalTheory.EisLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {j : ℕ}

def IsEisCont (C : Matrix (Fin n) (Fin j) E) (h : GAd σ J → ℝ≥0) (φ : GAd σ J → ℂ) (Eis : ℂ → GAd σ J → ℂ) : Prop :=
  (∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re → ∀ g,
    GlobalTheory.Eis.CosetConv (parFlag σ J C fun _ => 0) (ratPts σ J) (fun x => φ x * npow (h x) s) g ∧
    Eis s g = GlobalTheory.Eis.cosetSum (parFlag σ J C fun _ => 0) (ratPts σ J) (fun x => φ x * npow (h x) s) g) ∧
  ∀ s₀ : ℂ, ∃ (k : ℕ) (U : Set ℂ) (H : ℂ → GAd σ J → ℂ), U ∈ 𝓝 s₀ ∧
    (∀ s ∈ U, s ≠ s₀ → ∀ g, H s g = (s - s₀) ^ k * Eis s g) ∧ (∀ s ∈ U, IsSmoothModerate σ J (H s)) ∧
    ∀ μ, IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H s)) U

def Exchanges (C D : Matrix (Fin n) (Fin j) E) (w : GAd σ J) : Prop :=
  (∃ b : GL (Fin j) (AF F ⊗[F] E), (matHom _ σ J w).1 * adMat F C = adMat F D * b.1) ∧
  ∃ b : GL (Fin j) (AF F ⊗[F] E), (matHom _ σ J w).1 * adMat F D = adMat F C * b.1

end GlobalTheory.EisLine

namespace GlobalTheory.Published

def EisensteinFunctionalEquation : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    Algebra.Unramified (𝓞 F) (𝓞 E) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (j : ℕ) (hj : j ≤ r) (C D : Matrix (Fin n) (Fin j) E), C = X.submatrix id (Fin.castLE hj) →
        D = Y.submatrix id (Fin.castLE hj) →
      ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), IsAdapted σ J X Y L a →
      ∀ h : GAd σ J → ℝ≥0,
        (∀ (p : GAd σ J) (b : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * b.1 →
          ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E (Matrix.GeneralLinearGroup.det b)) →
      ∀ w ∈ ratPts σ J, Exchanges σ J C D w →
      ∀ (μ : Measure (unipRad σ J C)) (𝓕 : Set (unipRad σ J C)), μ.IsHaarMeasure →
        IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J C)) 𝓕 μ → μ 𝓕 = 1 →
      ∀ φ : GAd σ J → ℂ, IsAutOn σ J (leftGrp σ J C fun _ => 0) (levelAll σ J L a) φ →
      ∃ (m : ℕ) (ψ : Fin m → GAd σ J → ℂ) (c : Fin m → ℂ → ℂ) (σ₁ : ℝ),
        (∀ i, IsAutOn σ J (leftGrp σ J C fun _ => 0) (levelAll σ J L a) (ψ i)) ∧ (∀ i, MeromorphicOn (c i) Set.univ) ∧
        (∀ s : ℂ, σ₁ < s.re → ∀ g,
          Integrable (fun u : unipRad σ J C => φ (w * u * g) * npow (h (w * u * g)) s) μ ∧
          ∫ u : unipRad σ J C, φ (w * u * g) * npow (h (w * u * g)) s ∂μ = (∑ i, c i s * ψ i g) * npow (h g) (-s)) ∧
        ∀ (Eis : ℂ → GAd σ J → ℂ) (Es : Fin m → ℂ → GAd σ J → ℂ), IsEisCont σ J C h φ Eis →
          (∀ i, IsEisCont σ J C h (ψ i) (Es i)) →
          ∀ s₀ : ℂ, ∀ᶠ s in 𝓝[≠] s₀, ∀ g, Eis s g = ∑ i, c i s * Es i (-s) g

end GlobalTheory.Published

end
