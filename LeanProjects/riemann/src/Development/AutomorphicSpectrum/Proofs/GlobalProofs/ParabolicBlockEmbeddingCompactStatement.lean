import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicBlockEmbeddingCompact
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minimal_parabolic_unipotent_levi_decomp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)), ∀ p ∈ PositivityTheory.ThKR.minPar σ J X, ∃ u ∈ GlobalTheory.StdPar.unip σ J X S, ∃ l ∈ GlobalTheory.StdPar.levi σ J X Y S, p = u * l := by
  first | exact @GlobalTheory.CompanionTheory.Glob.MinParLevi.minPar_eq_unip_mul_levi | exact GlobalTheory.CompanionTheory.Glob.MinParLevi.minPar_eq_unip_mul_levi | (intros; apply GlobalTheory.CompanionTheory.Glob.MinParLevi.minPar_eq_unip_mul_levi <;> assumption)
