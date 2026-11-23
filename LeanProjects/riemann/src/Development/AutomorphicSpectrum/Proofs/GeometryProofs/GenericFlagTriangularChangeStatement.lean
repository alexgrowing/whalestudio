import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagTriangularChange
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_flag_triangular_change : ∀ (L Li : Type) [Field L] [AddCommGroup Li] [Module L Li] (r : ℕ) (f b g : Fin r → Li) (v w : Matrix (Fin r) (Fin r) L), LinearIndependent L f → LinearIndependent L b → (∀ k, v k k = 1) → (∀ l k, l < k → v l k = 0) → (∀ l k, k < l → w l k = 0) → (∀ k, w k k ≠ 0) → (∀ k, g k = ∑ j, (v * w) j k • f j) → (∀ i : ℕ, GlobalTheory.CompanionTheory.Ar.flagStep L b i = GlobalTheory.CompanionTheory.Ar.flagStep L g i) → ∃ Tm : Matrix (Fin r) (Fin r) L, (∀ i, b i = ∑ m, Tm i m • ∑ j, v j m • f j) ∧ (∀ i m, i < m → Tm i m = 0) ∧ ∀ i, Tm i i ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagChange.adapted_triangular | exact GlobalTheory.CompanionTheory.Ar.FlagChange.adapted_triangular | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagChange.adapted_triangular <;> assumption)
