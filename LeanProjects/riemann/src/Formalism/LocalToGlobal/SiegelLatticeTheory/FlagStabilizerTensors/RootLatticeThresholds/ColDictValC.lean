import Mathlib
import Formalism.LocalRingCardinality.DataCoeff

noncomputable section

namespace Formalism.L2.SG.Pf.ColDictPf

open Formalism.BasicNotions Matrix
open scoped ComplexOrder

section Copies

variable {ι : Type} [Fintype ι]

def tenV {R : Type} [CommRing R] {n : ℕ} (f : ι → MvPolynomial (Fin n × Fin n) R) :
    MvPolynomial (ι × Fin n × Fin n) R :=
  ∏ τ, MvPolynomial.rename (Prod.mk τ) (f τ)

def CSpanV {n : ℕ} (lam : ι → DomWeight n) : Submodule ℂ (MvPolynomial (ι × Fin n × Fin n) ℂ) :=
  Submodule.span ℂ {p | ∃ f : ι → MvPolynomial (Fin n × Fin n) ℂ, (∀ τ, f τ ∈ delSq ℂ n (lam τ)) ∧ p = tenV f}

variable {n : ℕ}

def FramesV (_G : ι → Matrix (Fin n) (Fin n) ℂ) : Type :=
  {y : ι → Matrix (Fin n) (Fin n) ℂ // ∀ τ, IsUnit (y τ).det}

def fnOfV (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) (M : ι → Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (ι × Fin n × Fin n) ℂ →ₗ[ℂ] (FramesV G → ℂ) where
  toFun P := fun y => (∏ τ, (M τ * y.1 τ).det ^ s τ) *
    MvPolynomial.eval (fun x : ι × Fin n × Fin n => (M x.1 * y.1 x.1) x.2.1 x.2.2) P
  map_add' P Q := by funext y; simp [mul_add]
  map_smul' c P := by funext y; simp [MvPolynomial.smul_eval]; ring

def shiftOfV (lam : ι → DomWeight n) : ι → ℤ := fun τ => (lam τ).detShift

def ValCV (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) : Submodule ℂ (FramesV G → ℂ) :=
  (CSpanV lam).map (fnOfV G (shiftOfV lam) 1)

end Copies

def ValCIrr : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ℕ) (G : ι → Matrix (Fin n) (Fin n) ℂ),
    (∀ τ, (G τ).PosDef ∨ (-G τ).PosDef) →
    ∀ (lam : ι → DomWeight n) (W : Submodule ℂ (FramesV G → ℂ)), W ≤ ValCV G lam → W ≠ ⊥ →
      (∀ g : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (g τ)ᴴ * G τ * g τ = G τ) →
        ∀ F ∈ W, ∃ F' ∈ W, ∀ y y' : FramesV G, (∀ τ, y'.1 τ = g τ * y.1 τ) → F' y = F y') →
      W = ValCV G lam

end Formalism.L2.SG.Pf.ColDictPf
