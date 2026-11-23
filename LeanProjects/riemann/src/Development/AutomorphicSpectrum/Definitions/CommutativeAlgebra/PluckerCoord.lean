import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor

namespace GlobalTheory.CompanionTheory.Ar.Num

noncomputable section

def pluckerIdx {J : Type} (N : ℕ) (M : J → ℕ) : J × Fin (N + 1) → Type := fun k => Fin k.2 → Fin (M k.1)

instance pluckerIdx.fintype {J : Type} (N : ℕ) (M : J → ℕ) (k : J × Fin (N + 1)) :
    Fintype (pluckerIdx N M k) := inferInstanceAs (Fintype (Fin k.2 → Fin (M k.1)))

variable {Ω : Type*} [Field Ω] {V : Type*} [AddCommGroup V] [Module Ω V]

def pluckerCoord {J : Type} {N : ℕ} {M : J → ℕ} (φ : ∀ j, Fin (M j) → Module.Dual Ω V) (w : Fin N → V) :
    (Σ k, pluckerIdx N M k) → Ω :=
  fun p => flagMinor (φ p.1.1) w p.1.2 (Nat.lt_succ_iff.mp p.1.2.2) p.2

def pluckerOmit {J : Type} {N : ℕ} {M : J → ℕ} (φ : ∀ j, Fin (M j) → Module.Dual Ω V) (w : Fin N → V)
    (i₀ : Fin (N + 1)) : (Σ k : {k : J × Fin (N + 1) // k.2 ≠ i₀}, pluckerIdx N M k.1) → Ω :=
  fun p => pluckerCoord φ w ⟨p.1.1, p.2⟩

def pluckerDeg {K J : Type} [DecidableEq J] {N : ℕ} (a : K → ℤ) (j : J) (i : Fin N) :
    K ⊕ (J × Fin (N + 1)) → ℤ :=
  Sum.elim a ((Pi.single (j, i.castSucc) 1 : J × Fin (N + 1) → ℤ) - Pi.single (j, i.succ) 1)

def unipFlag {N : ℕ} (e : Fin N → V) (a : Fin N → Fin N → Ω) : Fin N → V :=
  fun l => e l + ∑ m, if l < m then a m l • e m else 0

end

end GlobalTheory.CompanionTheory.Ar.Num
