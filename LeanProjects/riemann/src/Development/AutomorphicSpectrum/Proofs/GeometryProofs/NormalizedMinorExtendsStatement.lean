import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalizedMinorExtends
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitOfSumEqOne
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalized_minor_extends : ∀ {F : Type} [Field F] (O : Subring F) [IsLocalRing O] {n r : ℕ} (Y : Matrix (Fin n) (Fin r) F) (k : ℕ) (hk : k + 1 ≤ r) (I' : Fin (k + 1) → Fin n) (I : Fin k → Fin n), NormAt O Y (k + 1) hk I' → NormAt O Y k (Nat.le_of_succ_le hk) I → ∃ f : Fin k → Fin (k + 1), Function.Injective f ∧ NormAt O Y k (Nat.le_of_succ_le hk) (I' ∘ f) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.normAt_exchange | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.normAt_exchange | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.normAt_exchange <;> assumption)
