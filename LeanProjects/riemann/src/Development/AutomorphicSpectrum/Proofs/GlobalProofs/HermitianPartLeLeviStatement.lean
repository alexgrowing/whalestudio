import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianPartLeLevi
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsAdaptedEmpty
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_decomposition_hermitian_centralizer : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)), ∀ mm ∈ levi D.sp.cm.sig V.gram X Y T, ∃ mH ∈ uPart D.sp.cm.sig V.gram X Y T, ∃ mo ∈ levi D.sp.cm.sig V.gram X Y T, (∀ t ∈ uPart D.sp.cm.sig V.gram X Y T, t * mo = mo * t) ∧ mm = mH * mo := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.USplit.exists_split | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.USplit.exists_split | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.USplit.exists_split <;> assumption)
