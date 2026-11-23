import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
open scoped TensorProduct

namespace GlobalTheory.BZMir.Leib

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def WhitHeredity : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (X : Fin h → Type) [∀ a, AddCommGroup (X a)]
      [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)), (∀ a, IsSmooth (π a)) →
      Nonempty (TwJacquet (multiProd (stdBlocks d hd) π) (unipB k (Fin N)) (whitChar ψ N) ≃ₗ[ℂ]
        ⨂[ℂ] a, TwJacquet (π a) (unipB k (Fin (d a))) (whitChar ψ (d a)))

def GenericProdIff : Prop :=
  ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (X : Fin h → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)), (∀ a, IsSmooth (π a)) →
    (IsGeneric (multiProd (stdBlocks d hd) π) ↔ ∀ a, IsGeneric (π a))

def GenericProdIrr : Prop :=
  ∀ (h N : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), IsGeneric (prodIrr x hd) ↔ ∀ a, IsGeneric (x a).rep

def WhitRankProd : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (h N : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N),
      Module.finrank ℂ (TwJacquet (prodIrr x hd) (unipB k (Fin N)) (whitChar ψ N)) =
        ∏ a, Module.finrank ℂ (TwJacquet (x a).rep (unipB k (Fin (x a).1)) (whitChar ψ (x a).1))

end GlobalTheory.BZMir.Leib

end
