import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Filter Topology

noncomputable section

namespace GlobalTheory.FlagAr

open GlobalTheory.FlagPoly

variable {D : D7} (Y : ShimX D.what₂.Tau)

def setB (B : ℝ) : Finset ℕ :=
  ((Finset.range (⌊B⌋₊ + 1)).filter Nat.Prime) ∪
    (Nat.primeFactors (2 * (NumberField.discr D.host.E).natAbs) ∪ Y.lev)

def IsLimDeg (B : ℝ) (Φ : Pol D.what₂.Tau Y.N →ₗ[ℝ] ℝ) : Prop :=
  ∀ F, Tendsto (fun R : ℝ => Y.arDeg (setB Y B) R F) atTop (𝓝 (Φ F))

def atWt (Φ : Pol D.what₂.Tau Y.N →ₗ[ℝ] ℝ) (lam : D.what₂.Tau → Fin Y.N → ℝ) : ℝ :=
  Φ (linRoot lam ^ (dimFl D.what₂.Tau Y.N + 1))

end GlobalTheory.FlagAr
