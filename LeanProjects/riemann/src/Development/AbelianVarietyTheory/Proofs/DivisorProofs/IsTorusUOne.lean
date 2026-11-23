import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThKSoDecay

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IsFrameU (σ : E →ₐ[F] E) {n q : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin q → Fin n → E) : Prop :=
  (∀ i j, form σ J (x i) (x j) = 0) ∧ (∀ i j, form σ J (y i) (y j) = 0) ∧
    ∀ i j, form σ J (x i) (y j) = if i = j then 1 else 0

def IsTorusU {σ : E →ₐ[F] E} {n q : ℕ} {J : Matrix (Fin n) (Fin n) E} (x y : Fin q → Fin n → E) (t : Fin q → ℝ)
    (a : UA σ J) : Prop :=
  (∀ i, (mat a - 1) *ᵥ incV F (x i) = realAd F (t i - 1) • incV F (x i)) ∧
  (∀ i, (mat a - 1) *ᵥ incV F (y i) = realAd F ((t i)⁻¹ - 1) • incV F (y i)) ∧
  ∀ z : Fin n → E, (∀ i, form σ J z (x i) = 0) → (∀ i, form σ J z (y i) = 0) → (mat a - 1) *ᵥ incV F z = 0

open scoped Classical in

abbrev semK (κ : Type) [Fintype κ] (k : ℕ) : Seminorm ℂ (SInf F κ) :=
  (Finset.Iic (k, k)).sup (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)

def SoDecayUnif : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ φ ∈ SB (Fin n × Fin d → Af F), (∀ f : SInf F (Fin n × Fin d), pureA F f φ ∈ M.So B.ψ B.τ₁) →
    ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ (f : SInf F (Fin n × Fin d)) g h,
      ‖theta om (pureA F f φ) g h‖ * (qht g : ℝ) ^ N ≤ C * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k

end GlobalTheory.ThKSoDecay
