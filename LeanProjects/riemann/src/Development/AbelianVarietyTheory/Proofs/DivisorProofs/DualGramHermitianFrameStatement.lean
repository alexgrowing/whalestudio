import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualGramHermitianFrame
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
theorem _root_.GlobalTheory.T.dual_gram_hermitian_frame : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (m : ι → ℕ) (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.PosDef → ∑ i, m i = g → ∀ (z : ∀ i, Fin (m i) → Fin g → ℂ) (G : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ), (∀ i, (G i).PosDef) → (∀ i b b', G i b b' = (Real.pi : ℂ) * hermForm Hm (z i b') (z i b)) → (∀ i i' b b', i ≠ i' → hermForm Hm (z i b) (z i' b') = 0) → ∀ c c' : Fin g → ℂ, HermFrame.form (HermFrame.dualGram ((Real.pi : ℂ) • Hm)) c c' = ∑ i, HermFrame.form (G i)⁻¹ (fun b => ∑ a, z i b a * c a) (fun b => ∑ a, z i b a * c' a) := by
  first | exact @GlobalTheory.DualEigenSum.form_dualGram_eq_sum | exact GlobalTheory.DualEigenSum.form_dualGram_eq_sum | (intros; apply GlobalTheory.DualEigenSum.form_dualGram_eq_sum <;> assumption)
