import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData

noncomputable section

namespace Formalism.MainNotions.J

section MatTransport

open Matrix

variable {p q n : ℕ} (e : (Fin p ⊕ Fin q) ≃ Fin n) (ε : Fin n → Bool)

def trIx (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) : Matrix (Fin n) (Fin n) ℂ := Matrix.reindex e e M

end MatTransport

open Formalism.BasicNotions.TH Formalism.MainNotions.S
open scoped Matrix

def DSTieAt (X : ProvA) (p q : ℕ) (lam : Ix p q → ℚ) (e : Ix p q ≃ Fin (p + q)) (ε : Fin (p + q) → Bool)
    (lamS : Fin (p + q) → ℝ) (c : ℝ)
    (σ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ → ((X.ds p q lam).U.H →L[ℂ] (X.ds p q lam).U.H))
    (χ : (X.grp p q).G → ℂ) (E : (X.ds p q lam).U.H →L[ℂ] (X.ds p q lam).U.H) : Prop :=
    (∀ a, ε (e a) = a.isLeft) ∧ (∀ a, lamS (e a) = (lam a : ℝ) + c) ∧ Formalism.QuantumDeterminants.IsHCParam lamS ∧
    IsDS ε lamS σ ∧ (∀ g, ‖χ g‖ = 1) ∧ (∀ Y ∈ pR p q, χ ((X.grp p q).expt Y) = 1) ∧
    (∀ g, (X.ds p q lam).U.π g = χ g • σ (trIx e (((X.grp p q).cov g : GL (Ix p q) ℂ) : Mat p q))) ∧
    Formalism.MainNotions.SchurIrreducible.isoVec (X.ds p q lam) (blattner lam) ⊆ (lowKSub ε lamS σ : Set (X.ds p q lam).U.H) ∧
    IsOrthProjOnto E (lowKSub ε lamS σ)

def DSTie (X : ProvA) (p q : ℕ) (lam : Ix p q → ℚ) : Prop :=
  ∃ e ε lamS c σ χ E, DSTieAt X p q lam e ε lamS c σ χ E

def DSTies (X : ProvA) : Prop := ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → DSTie X p q lam

section Transport

variable {p q : ℕ} (e : Ix p q ≃ Fin (p + q)) (ε : Fin (p + q) → Bool) (hε : ∀ a, ε (e a) = a.isLeft)

include hε

end Transport

end Formalism.MainNotions.J

end
