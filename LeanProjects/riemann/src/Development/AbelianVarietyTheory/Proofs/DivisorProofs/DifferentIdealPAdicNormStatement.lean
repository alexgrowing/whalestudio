import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentIdealPAdicNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.different_ideal_p_adic_norm : ∀ (E : Type) [Field E] [NumberField E], IsGalois ℚ E → ∃ (m : ℕ) (d : Fin m → 𝓞 E), (∃ n : ℕ, n ≠ 0 ∧ (n : 𝓞 E) ∈ Ideal.span (Set.range d)) ∧ ∀ (p : ℕ) [Fact p.Prime] (φ : 𝓞 E →+* ↥(intO ℂ_[p])), ‖fun k => ((φ (d k) : ↥(intO ℂ_[p])) : ℂ_[p])‖ = (p : ℝ) ^ (-vDiff E p) := by
  first | exact @GlobalTheory.DiffGenNorm.exists_diffGens_norm | exact GlobalTheory.DiffGenNorm.exists_diffGens_norm | (intros; apply GlobalTheory.DiffGenNorm.exists_diffGens_norm <;> assumption)
