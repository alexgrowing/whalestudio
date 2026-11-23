import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagHomKeepsRadical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPtGenMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open CategoryTheory.Limits

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_hom_keeps_radical : ∀ (Y : GlobalTheory.ProjVar.Var ℚ) (φ : (GlobalTheory.ProjVar.proj ℚ 0).Fn →ₐ[ℚ] Y.Fn), (GlobalTheory.FlagBundle.ratOf (GlobalTheory.ProjVar.proj ℚ 0)).IsHom (GlobalTheory.FlagBundle.ratOf Y) φ (GlobalTheory.FlagQ.toPt Y) → GlobalTheory.FlagBundle.KeepsRad (GlobalTheory.FlagBundle.ratOf (GlobalTheory.ProjVar.proj ℚ 0)) (GlobalTheory.FlagBundle.ratOf Y) φ (GlobalTheory.FlagQ.toPt Y) := by
  first | exact @GlobalTheory.FlagQ.keepsRad_toPt | exact GlobalTheory.FlagQ.keepsRad_toPt | (intros; apply GlobalTheory.FlagQ.keepsRad_toPt <;> assumption)
