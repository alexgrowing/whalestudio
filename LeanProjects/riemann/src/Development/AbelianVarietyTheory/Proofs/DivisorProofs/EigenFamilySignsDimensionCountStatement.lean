import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFamilySignsDimensionCount
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFlagged
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleSectionLiftsMetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLineBundleInducedArith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleMetricSetupStatement
open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.DegreeFormula GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TwoLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_family_signs_dimension_count : ∀ (D : D7) (O : Setup D), ∃ (ix : GlobalTheory.EigWhole.Var O → Letter O.S.Dw ⊕ Letter O.S.Dw) (sg : GlobalTheory.EigWhole.Var O → ℤ) (n e : ℕ) (Q : MvPolynomial (Letter O.S.Dw) ℝ), n + 1 = dimGr D.what₂.Tau O.N O.j ∧ n + 1 + e = dimFl D.what₂.Tau O.N ∧ (∀ i, sg i = 1 ∨ sg i = -1) ∧ (∀ (R : ℝ) i, (∃ z, ix i = .inl z ∧ GlobalTheory.EigWhole.fam O ∅ R i = Finsupp.single (ArIn.ind ∅, some R, .inl (z.1, (z.2 : ℕ))) (sg i)) ∨ ∃ z k, ix i = .inr z ∧ (letters O.S.Dw)[k]? = some z ∧ GlobalTheory.EigWhole.fam O ∅ R i = Finsupp.single (ArIn.ind ∅, some R, .inr k) (sg i)) ∧ Q.IsHomogeneous e ∧ GlobalTheory.GoodMetric.antisymm Q = 0 ∧ (GlobalTheory.EigWholeDR.diffPolDR O).IsHomogeneous (n + 1 + e + 1) ∧ aeval (fun i => (C (sg i : ℝ) * X (ix i) : MvPolynomial (Letter O.S.Dw ⊕ Letter O.S.Dw) ℝ)) (GlobalTheory.EigWholeDR.diffPolDR O) = (∑ z, X (Sum.inr z) ^ 2 - ∑ z, X (Sum.inl z) ^ 2) * rename Sum.inl ((∑ z, X z) ^ n * Q) := by
  first | exact @GlobalTheory.RelabDR.relabel_diffPolDR | exact GlobalTheory.RelabDR.relabel_diffPolDR | (intros; apply GlobalTheory.RelabDR.relabel_diffPolDR <;> assumption)
