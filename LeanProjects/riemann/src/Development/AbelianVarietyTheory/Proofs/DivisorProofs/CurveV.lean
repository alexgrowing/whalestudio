import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne

set_option autoImplicit false

noncomputable section

open MvPolynomial Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula GlobalTheory.FlagPoly

namespace GlobalTheory.CovTestDR

def vdmCl (ι : Type) [Fintype ι] (N j : ℕ) : Pol ι N :=
  ∏ τ : ι, ((C ((Nat.factorial j : ℝ)⁻¹) *
      ∏ a : Fin N, ∏ b : Fin N, if a < b ∧ (b : ℕ) < j then X (τ, b) - X (τ, a) else 1) *
    (C ((Nat.factorial (N - j) : ℝ)⁻¹) *
      ∏ a : Fin N, ∏ b : Fin N, if a < b ∧ j ≤ (a : ℕ) then X (τ, b) - X (τ, a) else 1))

def curveV (ι : Type) [Fintype ι] (N j : ℕ) : Pol ι N := lamA ι N j ^ (dimGr ι N j - 1) * vdmCl ι N j

variable {D : D7} (Y : ShimX D.what₂.Tau)

def vdmVal (R : ℝ) : ℝ :=
  Y.arMix ∅ R 1 (X (Sum.inr (false, 2)) * tagDR D.what₂.Tau _ (curveV D.what₂.Tau Y.N Y.j))

example (ι : Type) [Fintype ι] : vdmCl ι 3 1 = ∏ τ : ι, (C (1 : ℝ) * 1 * (C ((2 : ℝ)⁻¹) * (X (τ, 2) - X (τ, 1)))) := by
  unfold vdmCl
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp [Fin.prod_univ_three, Nat.factorial]

end GlobalTheory.CovTestDR

end
