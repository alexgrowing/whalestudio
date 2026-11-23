import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime

noncomputable section

open PowerSeries

namespace GlobalTheory.Col

variable {R : Type} [CommRing R]

def pmeas (p r : ℕ) (g : PowerSeries R) (x : ℕ) : R :=
  ∑ m ∈ Finset.range (r + 1), Algebra.trace R (lev R p m) (ev R p m ((1 + X) ^ (p ^ r - x % p ^ r) * g))

def intU (p r : ℕ) [NeZero p] (η : (ZMod (p ^ r))ˣ → R) (g : PowerSeries R) : R :=
  ∑ b : (ZMod (p ^ r))ˣ, η b * pmeas p r g (b : ZMod (p ^ r)).val

def colMeas (p : ℕ) [hp : Fact p.Prime] (a : Rˣ) (g : PowerSeries R) : PowerSeries R :=
  g - PowerSeries.C (↑a⁻¹ : R) * phi (R := R) p hp.out.pos g

def chSum (p m : ℕ) [NeZero p] (ch : (ZMod (p ^ m))ˣ →* Rˣ) (g : PowerSeries R) : lev R p m :=
  ∑ b : (ZMod (p ^ m))ˣ, ev R p m (PowerSeries.C (ch b : R) * sb (b : ZMod (p ^ m)).val g)

def gauss (p m : ℕ) [NeZero p] (ch : (ZMod (p ^ m))ˣ →* Rˣ) : lev R p m :=
  ∑ b : (ZMod (p ^ m))ˣ, ev R p m (PowerSeries.C (ch b : R) * (1 + X) ^ (b : ZMod (p ^ m)).val)

end GlobalTheory.Col
