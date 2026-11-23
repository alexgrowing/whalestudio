import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartUniformBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoUniformlyOfFamAt
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec GlobalTheory.MetFam GlobalTheory.ShFam GlobalTheory.Toroidal GlobalTheory.CxPts
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_part_uniform_bound : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ t : ℝ → ℝ, Tendsto t atTop (𝓝 0) → ∀ (σ : k →+* ℂ) (B : LB X) (φ : Weight p σ B), φ.IsCInf → ∀ u : ℝ → CxPts p σ → ℝ, (∀ R y, CInfAt (u R) y) → (∀ y, FamAt t u (fun _ => 0) y) → ∃ C : NNReal, ∀ᶠ R in atTop, ∀ ε : ℤˣ, (φ.addFn (u R)).chernPart D ε Set.univ ≤ (C : ENNReal) := by
  first | exact @GlobalTheory.MetFam.exists_bound_chernPart_univ | exact GlobalTheory.MetFam.exists_bound_chernPart_univ | (intros; apply GlobalTheory.MetFam.exists_bound_chernPart_univ <;> assumption)
