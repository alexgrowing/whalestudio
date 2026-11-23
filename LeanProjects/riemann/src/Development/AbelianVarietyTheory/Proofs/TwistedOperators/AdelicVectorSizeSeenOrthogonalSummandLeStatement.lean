import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicVectorSizeSeenOrthogonalSummandLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VsizeNonneg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicVectorSize_seen_orthogonalSummand_le : ∀ (D : D7) (S A B : HSp D) (o : GlobalTheory.MixModel.OrthDec S A B), ∃ C : ℝ, ∀ (h : GA D A) (η : Fin A.rank → D.host.E), GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen S (o.emb (h, 1)) (o.iA *ᵥ η)) ≤ C * GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen A h η) := by
  first | exact @GlobalTheory.HtOrth.Transp.vsize_seen_emb_le | exact GlobalTheory.HtOrth.Transp.vsize_seen_emb_le | (intros; apply GlobalTheory.HtOrth.Transp.vsize_seen_emb_le <;> assumption)
