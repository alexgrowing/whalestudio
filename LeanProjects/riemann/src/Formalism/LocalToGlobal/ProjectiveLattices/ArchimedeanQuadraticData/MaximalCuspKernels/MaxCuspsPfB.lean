import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SublatticeCoefficients

set_option autoImplicit false

noncomputable section

open MeasureTheory Complex

namespace Formalism.L2.Pj.QAt

abbrev mcBox (n : ℕ) : Set (Fin n → ℝ) := Set.univ.pi fun _ : Fin n => Set.Ioc (0 : ℝ) 1

def mcE {n : ℕ} (m : Fin n → ℤ) (u : Fin n → ℝ) : ℂ :=
  cexp (-(2 * Real.pi * I) * ∑ j, (m j : ℂ) * (u j : ℂ))

def mcCo {n : ℕ} (g : (Fin n → ℝ) → ℂ) (m : Fin n → ℤ) : ℂ := ∫ u in mcBox n, g u * mcE m u

def mcT {n N : ℕ} (c : Fin n → Fin N → ℤ) (t : Fin n → ℝ) : Fin N → ℝ :=
  fun i => ∑ j, t j * (c j i : ℝ)

def mcG {n N : ℕ} (g : (Fin N → ℝ) → ℂ) (c : Fin n → Fin N → ℤ) (k : Fin n → ℤ)
    (u : Fin N → ℝ) : ℂ :=
  mcCo (fun t => g (u + mcT c t)) k

end Formalism.L2.Pj.QAt
