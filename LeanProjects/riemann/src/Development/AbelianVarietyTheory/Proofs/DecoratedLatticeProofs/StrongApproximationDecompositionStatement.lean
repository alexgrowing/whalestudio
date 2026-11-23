import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecomposition
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strong_approximation_decomposition : GlobalTheory.Published.StrongApproxSU → ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n), V.gram = 1 → ∀ g ∈ GfC V, ∃ r s k, IsRatFin V r ∧ s ∈ splitPart V ∧ k ∈ GfC V ∧ Moves V hn k (Formalism.L2.Col.stdLat D.host.E n) ∧ g = r * s * k := by
  first | exact @GlobalTheory.SplitDec.exists_rat_split_stab | exact GlobalTheory.SplitDec.exists_rat_split_stab | (intros; apply GlobalTheory.SplitDec.exists_rat_split_stab <;> assumption)
