import Mathlib
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.WeilPolarization.StdFormOneNondegenerate
import GroundTheory.GlobalFields.TateThesis.AdelicChar

namespace GroundTheory.Heights₂.Theta

open GroundTheory.Global NumberField MeasureTheory TensorProduct
open scoped NumberField.AdeleRing ComplexOrder

noncomputable section

section Alg

variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

def IsLagrangian (ω : LinearMap.BilinForm R W) (L : Submodule R W) : Prop :=
  ω.orthogonal L = L

variable {P₁ P₂ Q₁ Q₂ : Type*} [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂]
  [AddCommGroup Q₁] [Module R Q₁] [AddCommGroup Q₂] [Module R Q₂]

namespace FourPieces

variable {ω : LinearMap.BilinForm R W}

def incP₂ (F : FourPieces ω P₁ P₂ Q₁ Q₂) : P₂ →ₗ[R] W :=
  F.e.symm.toLinearMap ∘ₗ LinearMap.inl R (P₁ × P₂) (Q₁ × Q₂) ∘ₗ LinearMap.inr R P₁ P₂

def incQ₂ (F : FourPieces ω P₁ P₂ Q₁ Q₂) : Q₂ →ₗ[R] W :=
  F.e.symm.toLinearMap ∘ₗ LinearMap.inr R (P₁ × P₂) (Q₁ × Q₂) ∘ₗ LinearMap.inr R Q₁ Q₂

theorem incP₂_apply (F : FourPieces ω P₁ P₂ Q₁ Q₂) (p : P₂) :
    F.incP₂ p = F.e.symm ((0, p), (0, 0)) := rfl

theorem incQ₂_apply (F : FourPieces ω P₁ P₂ Q₁ Q₂) (q : Q₂) :
    F.incQ₂ q = F.e.symm ((0, 0), (0, q)) := rfl

theorem form_incP₂_incQ₂ (F : FourPieces ω P₁ P₂ Q₁ Q₂) (p : P₂) (q : Q₂) :
    ω (F.incP₂ p) (F.incQ₂ q) = F.a₂ p q := by
  rw [F.form, incP₂_apply, incQ₂_apply]
  simp

end FourPieces

end Alg

section Adelic

variable (K : Type*) [Field K] [NumberField K]

variable (P Q : Type*) [AddCommGroup P] [Module K P] [AddCommGroup Q] [Module K Q] in

abbrev adelicProdEquiv : AdelicPoints K (P × Q) ≃ₗ[𝔸[K]] AdelicPoints K P × AdelicPoints K Q :=
  TensorProduct.prodRight K 𝔸[K] 𝔸[K] P Q

variable {K}
variable {W P₁ P₂ Q₁ Q₂ : Type*} [AddCommGroup W] [Module K W]
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup Q₁] [Module K Q₁] [AddCommGroup Q₂] [Module K Q₂]

namespace FourPieces

variable {ω : LinearMap.BilinForm K W}

def adelicPairing₂ (F : FourPieces ω P₁ P₂ Q₁ Q₂) (p : AdelicPoints K P₂) (q : AdelicPoints K Q₂) :
    𝔸[K] :=
  ω.baseChange 𝔸[K] (F.incP₂.baseChange 𝔸[K] p) (F.incQ₂.baseChange 𝔸[K] q)

theorem adelicPairing₂_tmul (F : FourPieces ω P₁ P₂ Q₁ Q₂) (a a' : 𝔸[K]) (p : P₂) (q : Q₂) :
    F.adelicPairing₂ (a ⊗ₜ p) (a' ⊗ₜ q) = algebraMap K 𝔸[K] (F.a₂ p q) * (a * a') := by
  rw [adelicPairing₂, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
    LinearMap.BilinForm.baseChange_tmul, form_incP₂_incQ₂, Algebra.smul_def]

variable [FiniteDimensional K P₁] [FiniteDimensional K P₂] [FiniteDimensional K Q₂]

def adelicPartialFourier (ψ : AddChar 𝔸[K] Circle) (F : FourPieces ω P₁ P₂ Q₁ Q₂)
    (φ : AdelicPoints K (P₁ × P₂) → ℂ) : AdelicPoints K (P₁ × Q₂) → ℂ :=
  fun z ↦ ∫ p : AdelicPoints K P₂,
    φ ((adelicProdEquiv K P₁ P₂).symm ((adelicProdEquiv K P₁ Q₂ z).1, p)) *
      (ψ (F.adelicPairing₂ p (adelicProdEquiv K P₁ Q₂ z).2) : ℂ) ∂adelicPointsMeasure K P₂

def adelicPartialFourierInv (ψ : AddChar 𝔸[K] Circle) (F : FourPieces ω P₁ P₂ Q₁ Q₂)
    (Φ : AdelicPoints K (P₁ × Q₂) → ℂ) : AdelicPoints K (P₁ × P₂) → ℂ :=
  fun z ↦ ∫ q : AdelicPoints K Q₂,
    Φ ((adelicProdEquiv K P₁ Q₂).symm ((adelicProdEquiv K P₁ P₂ z).1, q)) *
      (ψ (-F.adelicPairing₂ (adelicProdEquiv K P₁ P₂ z).2 q) : ℂ) ∂adelicPointsMeasure K Q₂

end FourPieces

end Adelic

def PartialFourierTheta.Statement : Prop :=
  ∀ (K W P₁ P₂ Q₁ Q₂ : Type) [Field K] [NumberField K] [AddCommGroup W] [Module K W]
    [AddCommGroup P₁] [Module K P₁] [FiniteDimensional K P₁]
    [AddCommGroup P₂] [Module K P₂] [FiniteDimensional K P₂]
    [AddCommGroup Q₁] [Module K Q₁] [AddCommGroup Q₂] [Module K Q₂] [FiniteDimensional K Q₂]
    (ψ : AddChar 𝔸[K] Circle), Continuous ψ → (∀ k : K, ψ (algebraMap K 𝔸[K] k) = 1) → ψ ≠ 1 →
    ∀ (ω : LinearMap.BilinForm K W), ω.IsAlt → ω.Nondegenerate →
    ∀ (F : FourPieces ω P₁ P₂ Q₁ Q₂) (φ : AdelicPoints K (P₁ × P₂) → ℂ),
      φ ∈ schwartzBruhatPoints K (P₁ × P₂) →
        F.adelicPartialFourier ψ φ ∈ schwartzBruhatPoints K (P₁ × Q₂) ∧
          rationalTheta (F.adelicPartialFourier ψ φ) = rationalTheta φ

def PartialFourierInversion.Statement : Prop :=
  ∀ (K W P₁ P₂ Q₁ Q₂ : Type) [Field K] [NumberField K] [AddCommGroup W] [Module K W]
    [AddCommGroup P₁] [Module K P₁] [FiniteDimensional K P₁]
    [AddCommGroup P₂] [Module K P₂] [FiniteDimensional K P₂]
    [AddCommGroup Q₁] [Module K Q₁] [AddCommGroup Q₂] [Module K Q₂] [FiniteDimensional K Q₂]
    (ψ : AddChar 𝔸[K] Circle), Continuous ψ → (∀ k : K, ψ (algebraMap K 𝔸[K] k) = 1) → ψ ≠ 1 →
    ∀ (ω : LinearMap.BilinForm K W), ω.IsAlt → ω.Nondegenerate →
    ∀ (F : FourPieces ω P₁ P₂ Q₁ Q₂) (φ : AdelicPoints K (P₁ × P₂) → ℂ),
      φ ∈ schwartzBruhatPoints K (P₁ × P₂) →
        F.adelicPartialFourierInv ψ (F.adelicPartialFourier ψ φ) = φ

def LagrangianPairFourPieces.Statement : Prop :=
  ∀ (K W : Type) [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ω : LinearMap.BilinForm K W), ω.IsAlt → ω.Nondegenerate →
    ∀ L L' : Submodule K W, IsLagrangian ω L → IsLagrangian ω L' →
      ∃ (P₁ P₂ Q₁ Q₂ : Submodule K W) (F : FourPieces ω P₁ P₂ Q₁ Q₂),
        (∀ w, w ∈ L ↔ (F.e w).2 = 0) ∧ (∀ w, w ∈ L' ↔ (F.e w).1.2 = 0 ∧ (F.e w).2.1 = 0)

section Inhabitants

variable (R : Type*) [CommRing R]

def lineFourForm : LinearMap.BilinForm R ((R × R) × (R × R)) :=
  LinearMap.mk₂ R
    (fun w w' ↦ w.1.1 * w'.2.1 + w.1.2 * w'.2.2 - w'.1.1 * w.2.1 - w'.1.2 * w.2.2)
    (fun _ _ _ ↦ by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun _ _ _ ↦ by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
    (fun _ _ _ ↦ by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun _ _ _ ↦ by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)

theorem lineFourForm_apply (w w' : (R × R) × (R × R)) :
    lineFourForm R w w' = w.1.1 * w'.2.1 + w.1.2 * w'.2.2 - w'.1.1 * w.2.1 - w'.1.2 * w.2.2 := rfl

def lineFourPieces : FourPieces (lineFourForm R) R R R R where
  e := LinearEquiv.refl R _
  a₁ := LinearMap.mul R R
  a₂ := LinearMap.mul R R
  form w w' := by simp [lineFourForm_apply]

def lineFourLagrangian : Submodule R ((R × R) × (R × R)) :=
  LinearMap.ker (LinearMap.snd R (R × R) (R × R))

end Inhabitants

end

end GroundTheory.Heights₂.Theta
