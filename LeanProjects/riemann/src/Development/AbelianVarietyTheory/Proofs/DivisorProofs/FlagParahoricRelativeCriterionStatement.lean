import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagParahoricRelativeCriterion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPtGenMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open CategoryTheory.Limits

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_parahoric_relative_criterion : ∀ {ι : Type} {m k : ι → ℕ} {K : Type} [Field K] (O : Subring K) (A B A' : GlobalTheory.FlagBundle.Mat m K), GlobalTheory.FlagBundle.Par 0 O A → GlobalTheory.FlagBundle.Par k ⊤ (A * B⁻¹) → (GlobalTheory.FlagBundle.Par 0 O A' ∧ GlobalTheory.FlagBundle.Par k ⊤ (A' * B⁻¹) ↔ GlobalTheory.FlagBundle.Par k O (A' * A⁻¹)) := by
  first | exact @GlobalTheory.FlagBundle.FrameChange.par_iff | exact GlobalTheory.FlagBundle.FrameChange.par_iff | (intros; apply GlobalTheory.FlagBundle.FrameChange.par_iff <;> assumption)
