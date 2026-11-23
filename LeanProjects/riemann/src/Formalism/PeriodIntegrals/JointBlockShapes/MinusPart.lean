import Mathlib

noncomputable section

open Matrix

namespace FockH1Action

abbrev Ix (p q : ℕ) := Fin p ⊕ Fin q

abbrev Mat (p q : ℕ) := Matrix (Ix p q) (Ix p q) ℂ

def Jpq (p q : ℕ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := Matrix.fromBlocks 1 0 0 (-1)

def Jm (p q : ℕ) : Mat p q := Jpq p q

def sameBlock {p q : ℕ} : Ix p q → Ix p q → Prop
  | .inl _, .inl _ => True
  | .inr _, .inr _ => True
  | _, _ => False

instance {p q : ℕ} (a b : Ix p q) : Decidable (sameBlock a b) := by
  cases a <;> cases b <;> simp only [sameBlock] <;> infer_instance

def IsKC {p q : ℕ} (X : Mat p q) : Prop := ∀ a b, ¬ sameBlock a b → X a b = 0

def IsPC {p q : ℕ} (X : Mat p q) : Prop := ∀ a b, sameBlock a b → X a b = 0

def adjZ {p q : ℕ} (Z : Mat p q) : Mat p q := Jm p q * Zᴴ * Jm p q

def conjR {p q : ℕ} (Z : Mat p q) : Mat p q := -(adjZ Z)

abbrev Ln (p q r s : ℕ) := Ix p q × Ix r s

abbrev Pol (p q r s : ℕ) := MvPolynomial (Ix p q × Ix r s) ℂ

def linePos {p q r s : ℕ} : Ln p q r s → Bool
  | (.inl _, .inl _) => true
  | (.inr _, .inr _) => true
  | _ => false

def lowB {p q r s : ℕ} (l : Ln p q r s) : Module.End ℂ (Pol p q r s) :=
  if linePos l then (MvPolynomial.pderiv l).toLinearMap
  else LinearMap.mulLeft ℂ (MvPolynomial.X l)

def raiB {p q r s : ℕ} (l : Ln p q r s) : Module.End ℂ (Pol p q r s) :=
  if linePos l then LinearMap.mulLeft ℂ (MvPolynomial.X l)
  else -(MvPolynomial.pderiv l).toLinearMap

def omE {p q r s : ℕ} (l l' : Ln p q r s) : Module.End ℂ (Pol p q r s) :=
  raiB l * lowB l' + if l = l' then (1 / 2 : ℂ) • 1 else 0

def omAct (p q r s : ℕ) :
    Matrix (Ln p q r s) (Ln p q r s) ℂ →ₗ[ℂ] Module.End ℂ (Pol p q r s) :=
  ∑ l, ∑ l', (Matrix.entryLinearMap ℂ ℂ l l').smulRight (omE l l')

def fockAct1 (p q r s : ℕ) : Mat p q →ₗ[ℂ] Module.End ℂ (Pol p q r s) :=
  omAct p q r s ∘ₗ (Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)).flip (1 : Mat r s)

def fockAct2 (p q r s : ℕ) : Mat r s →ₗ[ℂ] Module.End ℂ (Pol p q r s) :=
  omAct p q r s ∘ₗ (Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)) (1 : Mat p q)

section Grading

variable {σ : Type*}

def plusPart (A : Module.End ℂ (MvPolynomial σ ℂ)) (P : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  ∑ᶠ d : ℕ, MvPolynomial.homogeneousComponent (d + 2) (A (MvPolynomial.homogeneousComponent d P))

def minusPart (A : Module.End ℂ (MvPolynomial σ ℂ)) (P : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  ∑ᶠ d : ℕ, MvPolynomial.homogeneousComponent d (A (MvPolynomial.homogeneousComponent (d + 2) P))

abbrev homog (σ : Type*) (d : ℕ) : Submodule ℂ (MvPolynomial σ ℂ) :=
  MvPolynomial.homogeneousSubmodule σ ℂ d

open Classical in

def fockInner (P Q : MvPolynomial σ ℂ) : ℂ :=
  ∑ α ∈ P.support, ∑ β ∈ Q.support, (starRingEnd ℂ) (MvPolynomial.coeff α P) * MvPolynomial.coeff β Q *
    (if α = β then α.prod (fun _ k => (k.factorial : ℂ)) else 0)

end Grading

def H1 : Prop := ∀ p q r s : ℕ,
  (∀ Z : Mat p q, IsKC Z → ∀ d, ∀ P ∈ homog (Ix p q × Ix r s) d, fockAct1 p q r s Z P ∈
    homog (Ix p q × Ix r s) d) ∧
  (∀ Z : Mat r s, IsKC Z → ∀ d, ∀ P ∈ homog (Ix p q × Ix r s) d, fockAct2 p q r s Z P ∈
    homog (Ix p q × Ix r s) d) ∧
  (∀ Z : Mat p q, IsPC Z → ∀ P, fockAct1 p q r s Z P =
    plusPart (fockAct1 p q r s Z) P + minusPart (fockAct1 p q r s Z) P) ∧
  (∀ Z : Mat r s, IsPC Z → ∀ P, fockAct2 p q r s Z P =
    plusPart (fockAct2 p q r s Z) P + minusPart (fockAct2 p q r s Z) P) ∧
  (∀ Z : Mat p q, IsPC Z → ∀ P Q : Pol p q r s,
    fockInner (plusPart (fockAct1 p q r s Z) P) Q = - fockInner P (minusPart (fockAct1 p q r s (conjR Z)) Q)) ∧
  (∀ Z : Mat r s, IsPC Z → ∀ P Q : Pol p q r s,
    fockInner (plusPart (fockAct2 p q r s Z) P) Q = - fockInner P (minusPart (fockAct2 p q r s (conjR Z)) Q))

end FockH1Action
