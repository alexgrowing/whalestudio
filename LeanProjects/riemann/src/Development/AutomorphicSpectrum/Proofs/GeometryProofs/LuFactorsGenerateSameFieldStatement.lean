import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LuFactorsGenerateSameField
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lu_factors_generate_same_field : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (n : ℕ) (A : Matrix (Fin n) (Fin n) K) (u v w : Matrix (Fin n) (Fin n) L), A.det ≠ 0 → (∀ k, u k k = 1) → (∀ l k, l < k → u l k = 0) → (∀ k, v k k = 1) → (∀ l k, l < k → v l k = 0) → (∀ l k, k < l → w l k = 0) → (∀ k, w k k ≠ 0) → A.map (algebraMap K L) * u = v * w → IntermediateField.adjoin K (Set.range fun p : Fin n × Fin n => u p.1 p.2) = IntermediateField.adjoin K (Set.range fun p : Fin n × Fin n => v p.1 p.2) := by
  first | exact @GlobalTheory.CompanionTheory.LuFields.adjoin_entries_eq | exact GlobalTheory.CompanionTheory.LuFields.adjoin_entries_eq | (intros; apply GlobalTheory.CompanionTheory.LuFields.adjoin_entries_eq <;> assumption)
