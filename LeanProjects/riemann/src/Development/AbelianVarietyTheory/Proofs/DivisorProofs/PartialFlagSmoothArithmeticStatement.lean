import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFlagSmoothArithmetic
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_flag_smooth_arithmetic : ∀ (ι κ : Type) [Fintype ι] [Finite κ] (N : ℕ) (a : κ → ι) (l : κ → Fin (N + 1)), SmoothOfRelativeDimension (Nat.card (CellVar a l)) (str a l) ∧ topologicalKrullDim (Part a l) = (Nat.card (CellVar a l) + 1 : ℕ) ∧ GlobalTheory.IsArithVar (str a l) (Nat.card (CellVar a l)) := by
  first | exact @GlobalTheory.FlagZ.smooth_dim_isArithVar_part | exact GlobalTheory.FlagZ.smooth_dim_isArithVar_part | (intros; apply GlobalTheory.FlagZ.smooth_dim_isArithVar_part <;> assumption)
