import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfAdelicHomDecomposeIsotropicMiddleComplement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfAdelicHom_decompose_isotropic_middle_complement : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ K : Matrix (Fin r) (Fin V.rank) D.host.E, K * C = 1 → K * B = 0 → ∀ (a : AE D) (u : WO V W), IsHalf a u → ∃ (y : Mx D W.rank r) (x : WO V' W) (t : Mx D W.rank r), IsHalf a y ∧ IsHalf a x ∧ IsHalf a t ∧ u = isoPart V W C y + midPart V V' W B x + restEmb V W K t := by
  first | exact @GlobalTheory.HalfDecomp.half_decomp | exact GlobalTheory.HalfDecomp.half_decomp | (intros; apply GlobalTheory.HalfDecomp.half_decomp <;> assumption)
