import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothAutomorphicDerivativeGrowth
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsAdaptedEmpty
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviNormalizesUnipotentVariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_restrict_smooth_moderate : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) → ∀ (Γ : Set (GA D V)) (ψ : GA D V → ℂ), IsSmModOn D.sp.cm.sig V.gram Γ ψ → ∀ y : GA D V, (∀ h, s h * y = y * s h) → (∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V'.rank) (Fin V'.rank) ℂ), (∀ i, Xs i ∈ lieAt V' (τs i)) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => ψ (s (g * (List.ofFn fun i => oneP θ V' (τs i) (Xs i) (t i)).prod) * y)) ∧ ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin V'.rank) (Fin V'.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V' p.1) → ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V', ‖(l.foldr (fun p f => Rder θ V' p.1 p.2 f) (fun h => ψ (s h * y))) (x * g)‖ ≤ C * normInf θ V' g ^ N := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.SliceReg.slice_regular | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.SliceReg.slice_regular | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.SliceReg.slice_regular <;> assumption)
