import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RationalUnipotentLeParabolic
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemFormsOnOfMemSpan
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_unipotent_le_parabolic : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ S T : Finset (Fin m), S ⊆ T → GQ V ⊓ unip D.sp.cm.sig V.gram X T ≤ leftSub V X Y S := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin.ratPts_unip_le_leftSub | exact GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin.ratPts_unip_le_leftSub | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin.ratPts_unip_le_leftSub <;> assumption)
