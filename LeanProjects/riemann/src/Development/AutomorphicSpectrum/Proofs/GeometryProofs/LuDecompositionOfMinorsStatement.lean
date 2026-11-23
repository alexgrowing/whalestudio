import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LuDecompositionOfMinors
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitOfSumEqOne
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lu_decomposition_of_minors : ∀ {F : Type} [Field F] {r : ℕ} (Y : Matrix (Fin r) (Fin r) F), (∀ (k : ℕ) (hk : k ≤ r), kMinor Y k hk (Fin.castLE hk) ≠ 0) → ∃ C V : Matrix (Fin r) (Fin r) F, (∀ l k, k < l → C l k = 0) ∧ (∀ l k, l < k → V l k = 0) ∧ (∀ l, V l l = 1) ∧ Y * C = V := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.exists_lu_of_leading_minors | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.exists_lu_of_leading_minors | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.exists_lu_of_leading_minors <;> assumption)
