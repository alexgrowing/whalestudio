import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MinimalParabolicUnipotentLeviDecomp
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsKInfEqMul
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_iwasawa_minimal_parabolic : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ g ∈ GinfC V, ∃ p ∈ PositivityTheory.ThKR.minPar D.sp.cm.sig V.gram X, ∃ κ : (∀ τ, Formalism.REAL.KG (ε τ)), g = p * GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.KInf.kInf θ V ε fr κ := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.ArchIwasawa.exists_archIwasawa | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.ArchIwasawa.exists_archIwasawa | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.ArchIwasawa.exists_archIwasawa <;> assumption)
