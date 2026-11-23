import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperFact

open MvPolynomial GlobalTheory.FlagPoly GlobalTheory.FlagForm

noncomputable section

namespace GlobalTheory.FlagCurve

def winSet (ι : Type) [Fintype ι] (N j : ℕ) : Finset (ι × Fin N × Fin N) :=
  Finset.univ.filter fun p => p.2.1 < p.2.2 ∧ ((p.2.2 : ℕ) < j ∨ j ≤ (p.2.1 : ℕ))

def crSet (ι : Type) [Fintype ι] (N j : ℕ) : Finset (ι × Fin N × Fin N) :=
  Finset.univ.filter fun p => p.2.1 < p.2.2 ∧ (p.2.1 : ℕ) < j ∧ j ≤ (p.2.2 : ℕ)

def mono {σ : Type} [DecidableEq σ] (R : Finset σ) : σ →₀ ℕ := ∑ s ∈ R, Finsupp.single s 1

end GlobalTheory.FlagCurve
