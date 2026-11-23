import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal

namespace GlobalTheory.EisRes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def col0 {n r : ℕ} (X : Matrix (Fin n) (Fin (r + 1)) E) : Matrix (Fin n) (Fin 1) E := X.submatrix id fun _ => 0

def IsIwaHtG (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) : Prop :=
  (∀ g, ∃ p, ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x ∧
    ∃ k ∈ levelAll σ J L a, g = p * k) ∧
  ∀ p, ∀ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x →
    ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E l

def HidaSetting (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin (r + 1)) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) : Prop :=
  IsCMExt F E σ ∧ Algebra.Unramified (𝓞 F) (𝓞 E) ∧ IsHermND σ J ∧ 4 ≤ n ∧ IsWittFrame σ J X Y ∧
    GlobalTheory.EisLine.IsAdapted σ J X Y L a ∧ IsIwaHtG σ J (col0 X) L a h

def IsSerG (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) (h : GAd σ J → ℝ)
    (Eis : ℂ → GAd σ J → ℂ) : Prop :=
  ∀ T : Set (ratPts σ J), (∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ∃ l : (AF F ⊗[F] E)ˣ,
      (matHom _ σ J (γ * t⁻¹ : ratPts σ J).1).1 * adMat F x = l.1 • adMat F x) →
    ∀ s : ℂ, ((n : ℝ) - 1) / 2 < s.re → ∀ g,
      HasSum (fun t : T => (h (t.1.1 * g) : ℂ) ^ (s + ((n : ℂ) - 1) / 2)) (Eis s g)

def EisensteinHyp (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Matrix (Fin n) (Fin 1) E) (h : GAd σ J → ℝ)
    (Eis : ℂ → GAd σ J → ℂ) (c : ℂ → ℂ) : Prop :=
  IsSerG σ J x h Eis ∧
  (∀ w ∈ ratPts σ J, (matHom _ σ J w).1 * adMat F y = adMat F x →
    ∀ (μ : Measure (unipRad σ J x)) (𝓕 : Set (unipRad σ J x)), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J x)) 𝓕 μ → μ 𝓕 = 1 →
      ∀ s : ℂ, ((n : ℝ) - 1) / 2 < s.re → ∀ g,
        Integrable (fun u : unipRad σ J x => (h (w * u * g) : ℂ) ^ (s + ((n : ℂ) - 1) / 2)) μ ∧
        ∫ u : unipRad σ J x, (h (w * u * g) : ℂ) ^ (s + ((n : ℂ) - 1) / 2) ∂μ =
          c s * (h g : ℂ) ^ (-s + ((n : ℂ) - 1) / 2)) ∧
  MeromorphicOn c Set.univ ∧
  (∀ s₀ : ℂ, ∃ (k : ℕ) (U : Set ℂ) (H : ℂ → GAd σ J → ℂ), U ∈ 𝓝 s₀ ∧
    (∀ s ∈ U, s ≠ s₀ → ∀ g, H s g = (s - s₀) ^ k * Eis s g) ∧ (∀ s ∈ U, IsSmoothModerate σ J (H s)) ∧
    ∀ μ, GlobalTheory.EisLine.IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H s)) U) ∧
  ∀ s₀ : ℂ, ∀ᶠ s in 𝓝[≠] s₀, c s * c (-s) = 1 ∧ ∀ g, Eis s g = c s * Eis (-s) g

def CoreConcl (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) (h : GAd σ J → ℝ)
    (Eis : ℂ → GAd σ J → ℂ) : Prop :=
  IsSerG σ J x h Eis ∧
  (∀ s₀ : ℂ, ∃ (k : ℕ) (U : Set ℂ) (Hol : ℂ → GAd σ J → ℂ) (C : ℝ) (N : ℕ), U ∈ 𝓝 s₀ ∧
    (∀ s ∈ U, s ≠ s₀ → ∀ g, Hol s g = (s - s₀) ^ k * Eis s g) ∧ (∀ g, DifferentiableOn ℂ (Hol · g) U) ∧
    ∀ s ∈ U, ∀ g, ‖Hol s g‖ ≤ C * (height σ J g : ℝ) ^ N) ∧
  ∃ U ∈ 𝓝 (-(((n : ℂ) - 1) / 2)), ∃ (C : ℝ) (N : ℕ), ∀ g, DifferentiableOn ℂ (Eis · g) U ∧
    (∀ s ∈ U, ‖Eis s g‖ ≤ C * (height σ J g : ℝ) ^ N) ∧ Eis (-(((n : ℂ) - 1) / 2)) g = 1

def EisCore : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), HidaSetting σ J X Y L a h → ∃ Eis, CoreConcl σ J (col0 X) h Eis

end GlobalTheory.EisRes

end
