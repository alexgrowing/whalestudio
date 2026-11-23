import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl

noncomputable section

open MvPolynomial GlobalTheory.FlagPoly

namespace GlobalTheory.FlagForm

variable {ι : Type} [Fintype ι] {N : ℕ}

abbrev FormPol (ι : Type) (N : ℕ) : Type := MvPolynomial (ι × Fin N × Fin N) ℝ

def rootForm (x : ι × Fin N) : FormPol ι N :=
  ∑ a : Fin N, (if a < x.2 then X (x.1, a, x.2) else 0) - ∑ b : Fin N, (if x.2 < b then X (x.1, x.2, b) else 0)

def toForm (P : Pol ι N) : FormPol ι N := aeval rootForm P

def volExp : (ι × Fin N × Fin N) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => if p.2.1 < p.2.2 then 1 else 0

def superFact (N : ℕ) : ℕ := ∏ k ∈ Finset.range N, k.factorial

def formDeg (ω : FormPol ι N) : ℝ := ω.coeff volExp / (superFact N : ℝ) ^ Fintype.card ι

def bcForm (τ : ι) : FormPol ι N := ∑ a : Fin N, ∑ b : Fin N, if a < b then X (τ, a, b) else 0

def blkForm (j : ℕ) (τ : ι) : FormPol ι N :=
  ∑ a : Fin N, ∑ b : Fin N, if a < b ∧ ((b : ℕ) < j ∨ j ≤ (a : ℕ)) then X (τ, a, b) else 0

end GlobalTheory.FlagForm
