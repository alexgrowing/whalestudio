import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction

noncomputable section

open scoped Matrix
open MeasureTheory PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.KLI

variable {m n : ℕ}

def mLc (a : Matrix (Fin n) (Fin n) ℂ) : M2 n := Matrix.fromBlocks a 0 0 (aᴴ)⁻¹

def nbLc (c : Matrix (Fin n) (Fin n) ℂ) : M2 n := Matrix.fromBlocks 1 0 c 1

def lFT (C s : ℂ) (g : (Fin m → Fin n → ℂ) → ℂ) : (Fin m → Fin n → ℂ) → ℂ :=
  fun u => C * ∫ v : Fin m → Fin n → ℂ,
    Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v

def chp (k : ℂ) (x : Matrix (Fin n) (Fin n) ℂ) (g : (Fin m → Fin n → ℂ) → ℂ) : (Fin m → Fin n → ℂ) → ℂ :=
  fun u => Complex.exp (2 * Real.pi * Complex.I * k * Matrix.trace (x * ((Matrix.of u)ᴴ * Matrix.of u))) * g u

abbrev LOp (m n : ℕ) : Type := GR n → ((Fin m → Fin n → ℂ) → ℂ) → (Fin m → Fin n → ℂ) → ℂ

def gZ (sg : ℤˣ) (Z : Matrix (Fin n) (Fin n) ℂ) (u : Fin m → Fin n → ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((sg : ℤ) : ℂ) * Matrix.trace (Z * ((Matrix.of u)ᴴ * Matrix.of u)))

def IsPG (sg : ℤˣ) (d : ℕ) (Z : Matrix (Fin n) (Fin n) ℂ) (f : (Fin m → Fin n → ℂ) → ℂ) : Prop :=
  ∃ Q : PX m n, Q.totalDegree ≤ d ∧ f = fun u => evX Q u * gZ sg Z u

def pOf (sg : ℤˣ) (m : ℕ) : ℕ := if sg = 1 then m else 0

def qOf (sg : ℤˣ) (m : ℕ) : ℕ := if sg = 1 then 0 else m

structure LocHyp (sg : ℤˣ) (L : LOp m n) : Prop where
  sw : ∀ y f, IsSw f → IsSw (L y f)
  one : ∀ f, IsSw f → L 1 f = f
  mul : ∀ y y' f, IsSw f → L (y * y') f = L y (L y' f)
  lin : ∀ y (a : ℂ) f g, IsSw f → IsSw g → L y (a • f + g) = a • L y f + L y g
  nU : ∀ (y : GR n) (b : Matrix (Fin n) (Fin n) ℂ), bᴴ = b → mR y = nU b → ∀ f, IsSw f →
    L y f = fun u => Complex.exp (2 * Real.pi * Complex.I * ((sg : ℤ) : ℂ) *
      Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) * f u
  mM : ∃ k : ℤ, ∀ (y : GR n) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → mR y = mLc a → ∀ f, IsSw f →
    L y f = fun u => (a.det / (‖a.det‖ : ℂ)) ^ k * (‖a.det‖ : ℂ) ^ m * f (Matrix.of u * a)
  nbar : ∃ (C s κ η : ℂ), s ≠ 0 ∧ κ ≠ 0 ∧ ‖s‖ = 2 ∧ η = -1 ∧
    (∀ f : (Fin m → Fin n → ℂ) → ℂ, IsSw f → lFT C s (lFT C s (lFT C s (lFT C s f))) = κ • f) ∧
    ∀ (y : GR n) (c : Matrix (Fin n) (Fin n) ℂ), cᴴ = c → mR y = nbLc c → ∀ f, IsSw f →
      L y f = κ⁻¹ • lFT C s (lFT C s (lFT C s (chp ((sg : ℤ) : ℂ) (η • c) (lFT C s f))))
  longWeylFunctional : ∃ C : ℂ, C ≠ 0 ∧ ∀ y : GR n, mR y = JJ n → ∀ f, IsSw f → L y f 0 = C * ∫ v, f v
  cont : ∀ (P : PX m n) u, Continuous fun y => L y (fP P) u

end PositivityTheory.SiegelWeilFormula.KLI

end
