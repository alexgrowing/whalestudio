import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagFrameParahoricAtPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPtGenMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open CategoryTheory.Limits

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_frame_parahoric_at_points : ∀ (ι : Type) [Fintype ι] (N : ℕ) (Y : GlobalTheory.ProjVar.Var ℚ) (j : Y.X ⟶ GlobalTheory.FlagZ.Fl ι N) (φ : (GlobalTheory.ProjVar.proj ℚ 0).Fn →ₐ[ℚ] Y.Fn), (GlobalTheory.FlagBundle.ratOf (GlobalTheory.ProjVar.proj ℚ 0)).IsHom (GlobalTheory.FlagBundle.ratOf Y) φ (GlobalTheory.FlagQ.toPt Y) → ∀ (z : Y.X) (A' : GlobalTheory.FlagBundle.Mat (fun _ : ι => N) Y.Fn), GlobalTheory.FlagQ.IsFrame j z A' → ∀ A ∈ (GlobalTheory.FlagQ.triv ι N).S (GlobalTheory.FlagQ.toPt Y z), GlobalTheory.FlagBundle.Par 0 ((GlobalTheory.FlagBundle.ratOf Y).O z).toSubring (A' * (A.map φ)⁻¹) := by
  first | exact @GlobalTheory.FlagQ.refines_sub | exact GlobalTheory.FlagQ.refines_sub | (intros; apply GlobalTheory.FlagQ.refines_sub <;> assumption)
