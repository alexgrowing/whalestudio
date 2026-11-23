import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermSmoothModerateGrowth
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemFormsOnOfMemSpan
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_smooth_moderate_growth : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (φ c : GA D V → ℂ), IsSmModOn D.sp.cm.sig V.gram ((GQ V ⊓ unip D.sp.cm.sig V.gram X T : Subgroup (GA D V)) : Set (GA D V)) φ → GlobalTheory.UAut.IsSm D.sp.cm.sig V.gram c → (∀ l : List (ℝ → GA D V), (∀ γ ∈ l, GlobalTheory.SiegelSet.IsRealLine D.sp.cm.sig V.gram γ) → IsConstAlong D.sp.cm.sig V.gram X T (l.foldr GlobalTheory.SiegelSet.lineDer φ) (l.foldr GlobalTheory.SiegelSet.lineDer c)) → ∀ (τ : D.what₂.Tau) (k : ℕ), IsConstAlong D.sp.cm.sig V.gram X T (gelf θ V τ k φ) (gelf θ V τ k c) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.ConstGelf.isConstAlong_gelf | exact GlobalTheory.CompanionTheory.Hypotheses₂.ConstGelf.isConstAlong_gelf | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.ConstGelf.isConstAlong_gelf <;> assumption)
