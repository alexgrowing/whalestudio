import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFlagSmoothArithmeticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellVarietyDimensionCountsStatement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula

namespace GlobalTheory.FlagZ

theorem isArithVar_hasHh_unique : ∀ (ι : Type) [Fintype ι] (N : ℕ), GlobalTheory.IsArithVar (flStr ι N) (dimFl ι N) ∧
    (GlobalTheory.Published.ArExists → HasHh ι N) ∧
    ∀ (h : HasHh ι N) (Φ : Pol ι N →ₗ[ℝ] ℝ), IsHh ι N Φ → Φ = hh h := by
  intro ι _ N
  have hd := GlobalTheory.T.partial_flag_smooth_arithmetic ι (ι × Fin (N + 1)) N Prod.fst Prod.snd
  rw [(GlobalTheory.T.cell_variety_dimension_counts ι N).1] at hd
  exact ⟨hd.2.2, fun H => ((H ℤ _ _ _ hd.2.2).2 _ grLine).1, fun _ _ hΦ => hΦ.eq_hh hd.2.1⟩

end GlobalTheory.FlagZ
