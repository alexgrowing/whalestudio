import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace Ysupp.Exp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

def zc (z : ℂˣ) : IrrGL k := IrrGL.ofChar (unrChar k z) (isSmoothChar_of_isUnram (isUnram_unrChar k z))

def IsTop {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (z : ℂˣ)
    (a : ℕ) : Prop :=
  (∃ w, wordMult π (List.replicate a z ++ w) ≠ 0) ∧ ∀ w, wordMult π (List.replicate (a + 1) z ++ w) = 0

def WordsSeparate : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (p : Fin n → IrrGL k) (c : Fin n → ℂ), Function.Injective p → (∀ i, ∃ w, wordMult (p i).rep w ≠ 0) →
      (∀ w, ∑ i, c i * ((wordMult (p i).rep w).toNat : ℂ) = 0) → ∀ i, c i = 0

def Deriv : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    IsSmooth π → π.IsIrreducible → ∀ (z : ℂˣ) (a : ℕ), 0 < a → IsTop π z a →
      ∃ (y : IrrGL k) (hd : ∑ j, (Fin.append (fun _ : Fin a => zc k z) ![y] j).1 = N),
        (∃ m : ℕ, 0 < m ∧ ∀ w, wordMult π (List.replicate a z ++ w) = (m : ℕ∞) * wordMult y.rep w) ∧
        (∀ w, wordMult y.rep (z :: w) = 0) ∧
        ∃ φ : π.IntertwiningMap (prodIrr (Fin.append (fun _ : Fin a => zc k z) ![y]) hd), Function.Injective φ

def Socle : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (z : ℂˣ) (a N : ℕ) (y : IrrGL k), (∃ w, wordMult y.rep w ≠ 0) → (∀ w, wordMult y.rep (z :: w) = 0) →
    ∀ (hd : ∑ j, (Fin.append (fun _ : Fin a => zc k z) ![y] j).1 = N)
      (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (GL (Fin N) k) V) (τ : Representation ℂ (GL (Fin N) k) W),
      π.IsIrreducible → τ.IsIrreducible →
      ∀ (φ : π.IntertwiningMap (prodIrr (Fin.append (fun _ : Fin a => zc k z) ![y]) hd))
        (ψ : τ.IntertwiningMap (prodIrr (Fin.append (fun _ : Fin a => zc k z) ![y]) hd)),
        Function.Injective φ → Function.Injective ψ → Nonempty (π.Equiv τ)

end Ysupp.Exp
