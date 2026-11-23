import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramMatrixOfMassFrameDiagonal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestFurther
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_matrix_of_mass_frame_diagonal : ∀ (D : D7) (i : Fin D.R.m), letI : IsCMField D.host.E := D.host.isCMField_hostE; ∃ (x : ReciprocityTheory.ChartRestriction.G.FD.Frame (GlobalTheory.MassLink.psi D) D.R.r) (p0 : GlobalTheory.MassLink.psi D → ℕ), ∀ τ : GlobalTheory.MassLink.psi D, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 (GlobalTheory.MassLink.gm D i) (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = Matrix.diagonal fun a : Fin D.R.r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn (p0 τ) (a : ℕ) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.OrthFrames.exists_orth_frames | exact GlobalTheory.OrthFrames.exists_orth_frames | (intros; apply GlobalTheory.OrthFrames.exists_orth_frames <;> assumption)
