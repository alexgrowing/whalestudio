import Mathlib
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.InvMod

noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4

namespace UpperTheory.Kd.K4

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def LUnH (X : Tower Ω ε) (H : Subgroup SL(2, ℤ)) (m : ℕ) (f : X.K) : Prop :=
  f ≠ 0 ∧ f ∈ lev X H ∧ ∀ W : ValuationSubring X.K, X.OverY W → ∃ c ∈ lev X H, c ≠ 0 ∧ W.valuation (f / c ^ m) = 1

def InvH (X : Tower Ω ε) (H : Subgroup SL(2, ℤ)) (m : ℕ) (a : X.Kˣ) : Prop :=
  ∀ γ ∈ H, ∃ h : X.Kˣ, X.sl (ofSL γ) (a : X.K) = a * (h : X.K) ^ m

def IsTr (H Γ : Subgroup SL(2, ℤ)) {ι : Type} (γ : ι → SL(2, ℤ)) : Prop :=
  (∀ i, γ i ∈ Γ) ∧ ∀ δ ∈ Γ, ∃! i, δ * (γ i)⁻¹ ∈ H

def sec (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w : ℕ) (lam : Fin 2 → ℤ) (a : X.Khat l) : X.Fn l :=
  fun u => ((lam 0 : ℤ_[l]) * u 0 + (lam 1 : ℤ_[l]) * u 1) ^ w • a

def trH (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w : ℕ) {ι : Type} [Fintype ι] (γ : ι → SL(2, ℤ)) (lam : Fin 2 → ℤ)
    (a : X.Khat l) : X.Fn l :=
  ∑ i, X.act l (γ i : Matrix (Fin 2) (Fin 2) ℤ) (sec X l w lam a)

end UpperTheory.Kd.K4

end
