import Mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Pb

variable {K R : Type} [Field K] [CommRing R] [Algebra K R] {d : ℕ}

def tpow (t : Fin d → Rˣ) (m : Fin d → ℤ) : R := ((∏ k, t k ^ m k : Rˣ) : R)

def expS (S : Finset (Fin (d + 1))) : Set (Fin d → ℤ) :=
  {m | (∀ k : Fin d, k.succ ∉ S → 0 ≤ m k) ∧ ((0 : Fin (d + 1)) ∉ S → ∑ k, m k ≤ 0)}

variable (K) in

def torusS (t : Fin d → Rˣ) (S : Finset (Fin (d + 1))) : Subalgebra K R := Algebra.adjoin K (tpow t '' expS S)

def jacS (B : Subalgebra K R) (D : Fin d → Derivation K R R) {m : ℕ} (κ : Fin m → Fin d) : AddSubgroup R :=
  AddSubgroup.closure {y | ∃ (b : B) (bs : Fin m → B), y = (b : R) * (Matrix.of fun k l => D (κ k) (bs l)).det}

end CrystallineSemistableComparison.Pb
