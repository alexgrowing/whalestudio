import Formalism.LogVandermondeBounds.FinrankFiberSumZero

namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts

open Finset

section Ops

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ}

def opGs (ψ : AddChar k ℂ) (φ : (Fin r → k) → ℂ) (f : Fin r → k) : ℂ :=
  ∑ c : kˣ, ψ (c : k) * φ ((c : k) • f)

def opGsStar (ψ : AddChar k ℂ) (φ : (Fin r → k) → ℂ) (f : Fin r → k) : ℂ :=
  ∑ c : kˣ, (starRingEnd ℂ) (ψ (c : k)) * φ (((c⁻¹ : kˣ) : k) • f)

def opFF (ψ : AddChar k ℂ) (φ : (Fin r → k) → ℂ) (x : Fin r → k) : ℂ :=
  ∑ f ∈ univ.filter (fun f => f ≠ 0), ψ (pair f x) * φ f

end Ops

def GaussOperatorProductFormula : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (r : ℕ) (ψ : AddChar k ℂ), ψ ≠ 1 →
    ∀ (φ : (Fin r → k) → ℂ) (f : Fin r → k),
      opGs ψ (opGsStar ψ φ) f = (Fintype.card k : ℂ) * φ f - nmP φ f

def FourierEqDownGauss : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (r : ℕ) (ψ : AddChar k ℂ),
    ∀ (φ : (Fin r → k) → ℂ), (∀ f, f ≠ 0 → nmP φ f = 0) →
      ∀ x : Fin r → k, opFF ψ φ x = opD (opGs ψ φ) x

def FourierIsometryNormKernel : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (r : ℕ) (ψ : AddChar k ℂ), ψ ≠ 1 →
    ∀ (φ φ' : (Fin r → k) → ℂ), (∀ f, f ≠ 0 → nmP φ f = 0) → (∀ f, f ≠ 0 → nmP φ' f = 0) →
      ∑ x ∈ univ.filter (fun x => x ≠ 0), (starRingEnd ℂ) (opFF ψ φ x) * opFF ψ φ' x =
        (Fintype.card k : ℂ) ^ r * ∑ f ∈ univ.filter (fun f => f ≠ 0), (starRingEnd ℂ) (φ f) * φ' f

def GaussOperatorAdjoint : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (r : ℕ) (ψ : AddChar k ℂ) (φ φ' : (Fin r → k) → ℂ),
    ∑ f, (starRingEnd ℂ) (opGs ψ φ f) * φ' f = ∑ f, (starRingEnd ℂ) (φ f) * opGsStar ψ φ' f

def FourierIntertwinesDiagonal : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (r : ℕ) (ψ : AddChar k ℂ),
    ∀ (φ : (Fin r → k) → ℂ) (c : kˣ), opFF ψ (diaP c φ) = diaV c (opFF ψ φ)

def FourierMapsNormKernel : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (r : ℕ) (ψ : AddChar k ℂ),
    ∀ (φ : (Fin r → k) → ℂ), (∀ f, f ≠ 0 → nmP φ f = 0) →
      ∀ x : Fin r → k, x ≠ 0 → nmV (opFF ψ φ) x = 0

end Formalism.LogVandermondeBounds.product_first_zeroth_parts
