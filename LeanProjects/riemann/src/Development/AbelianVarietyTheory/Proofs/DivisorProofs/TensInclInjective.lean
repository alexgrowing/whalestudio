import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdaptedFrame
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData

noncomputable section

open scoped TensorProduct Matrix
open NumberField Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.FockIncl

section Index

variable {R S : ℕ}

def skipIx (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1)) : Ix R S → Ix (R + 1) (S + 1)
  | .inl i => .inl (r₀.succAbove i)
  | .inr j => .inr (s₀.succAbove j)

theorem skipIx_injective (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1)) : Function.Injective (skipIx r₀ s₀) := by
  rintro (i | i) (j | j) h <;> simp_all [skipIx, Fin.succAbove_right_inj]

end Index

section Pol

variable (P Q : ℕ) {R S : ℕ}

def polIncl (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1)) : Formalism.BasicNotions.TH.Pol P Q R S →ₐ[ℂ] Formalism.BasicNotions.TH.Pol P Q (R + 1) (S + 1) :=
  MvPolynomial.rename (Prod.map id (skipIx r₀ s₀))

def harmTy (R S : ℕ) (x : ℚ) : Submodule ℂ (Formalism.BasicNotions.TH.Pol P Q R S) :=
  Submodule.span ℂ {f | f ∈ GlobalTheory.FockAlg.harm1 P Q R S ∧
    ∀ X : Mat P Q, IsKC X → fockAct1 P Q R S X f = ((x : ℂ) * X.trace) • f}

end Pol

section Tens

variable (F : Type) [Field F] [NumberField F] (P Q : ℕ) {R S : ℕ}

def tensIncl (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1)) : Tens F P Q R S →ₗ[ℂ] Tens F P Q (R + 1) (S + 1) :=
  PiTensorProduct.map fun _ => (polIncl P Q r₀ s₀).toLinearMap

def tensHarm (R S : ℕ) (x : InfinitePlace F → ℚ) : Submodule ℂ (Tens F P Q R S) :=
  Submodule.span ℂ {T | ∃ f : InfinitePlace F → Formalism.BasicNotions.TH.Pol P Q R S, (∀ w, f w ∈ harmTy P Q R S (x w)) ∧
    T = PiTensorProduct.tprod ℂ f}

end Tens

section Maps

variable {V Z : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup Z] [Module ℂ Z]

open Classical in

def leftInv (Φ : V →ₗ[ℂ] Z) : Z →ₗ[ℂ] V :=
  if h : Function.Injective Φ then Classical.choose (Φ.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 h)) else 0

end Maps

section Fock

variable {F : Type} [Field F] [NumberField F] {P Q R S : ℕ} {κ₁ κ : Type} [Fintype κ₁] [Fintype κ]

def fockIncl (Φ₁ : Tens F P Q R S →ₗ[ℂ] SInf F κ₁) (Φ : Tens F P Q (R + 1) (S + 1) →ₗ[ℂ] SInf F κ) (r₀ : Fin (R + 1))
    (s₀ : Fin (S + 1)) : SInf F κ₁ →ₗ[ℂ] SInf F κ :=
  Φ ∘ₗ tensIncl F P Q r₀ s₀ ∘ₗ leftInv Φ₁

end Fock

section Frames

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d d₁ R S : ℕ}

def IsCompat (B : Base F E) (H' : Plane E d d₁) (C : InfinitePlace F → Matrix (Fin d) (Ix (R + 1) (S + 1)) ℂ)
    (C₁ : InfinitePlace F → Matrix (Fin d₁) (Ix R S) ℂ) (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1)) : Prop :=
  ∀ w i c, C w i (skipIx r₀ s₀ c) = (H'.ι.map (B.emb w).1 * C₁ w) i c

def halfKap (B : Base F E) : InfinitePlace F → ℚ := fun w => ((B.mα w - B.mβ w : ℤ) : ℚ) / 2

end Frames

end GlobalTheory.FockIncl

namespace GlobalTheory.FockIncl
variable (F : Type) [Field F] [NumberField F] (P Q : ℕ) {R S : ℕ}

theorem tensIncl_injective (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1)) : Function.Injective (tensIncl F P Q r₀ s₀) := by
  have hi : Function.Injective (Prod.map (id : Ix P Q → Ix P Q) (skipIx r₀ s₀)) :=
    Function.Injective.prodMap Function.injective_id (skipIx_injective r₀ s₀)
  have hc : (PiTensorProduct.map fun _ : InfinitePlace F => (MvPolynomial.killCompl (R := ℂ) hi).toLinearMap) ∘ₗ
      tensIncl F P Q r₀ s₀ = LinearMap.id := by
    rw [tensIncl, ← PiTensorProduct.map_comp]
    have : ∀ _ : InfinitePlace F, (MvPolynomial.killCompl (R := ℂ) hi).toLinearMap ∘ₗ (polIncl P Q r₀ s₀).toLinearMap =
        LinearMap.id := fun _ => by
      rw [← AlgHom.comp_toLinearMap, polIncl, MvPolynomial.killCompl_comp_rename]; rfl
    rw [show (fun i : InfinitePlace F => (MvPolynomial.killCompl (R := ℂ) hi).toLinearMap ∘ₗ (polIncl P Q r₀ s₀).toLinearMap) = fun _ => LinearMap.id from funext this]
    exact PiTensorProduct.map_id
  intro a b hab
  have := congrArg (PiTensorProduct.map fun _ : InfinitePlace F => (MvPolynomial.killCompl (R := ℂ) hi).toLinearMap) hab
  simpa [← LinearMap.comp_apply, hc] using this

end GlobalTheory.FockIncl
