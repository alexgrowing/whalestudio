import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace Ysupp

def ProdSupport : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (c N : ℕ) (y : Fin c → IrrGL k) (hd : ∑ a, (y a).1 = N) (t : Fin c → Multiset (IrrGL k)),
    (∀ a, HasSupport (y a).rep (t a)) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
      π.IsIrreducible → IsSubquotient π (prodIrr y hd) → HasSupport π (∑ a, t a)

def SubEmbedding : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    IsSmooth π → π.IsIrreducible →
      ∃ (c : ℕ) (x : Fin c → IrrGL k) (hd : ∑ a, (x a).1 = N), (∀ a, (x a).IsCusp) ∧
        ∃ φ : π.IntertwiningMap (prodIrr x hd), Function.Injective φ

def PrinSeriesWord : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (c N : ℕ) (x : Fin c → IrrGL k) (hd : ∑ a, (x a).1 = N), (∀ a, (x a).IsUnramChar) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
      IsSmooth π → π.IsIrreducible → ∀ φ : π.IntertwiningMap (prodIrr x hd), Function.Injective φ →
        ∃ w, wordMult π w ≠ 0

end Ysupp
