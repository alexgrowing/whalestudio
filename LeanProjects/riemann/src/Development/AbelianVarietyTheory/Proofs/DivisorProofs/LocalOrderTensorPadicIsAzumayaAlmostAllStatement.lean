import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOrderTensorPadicIsAzumayaAlmostAll
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsScalarTowerCenAlgebra
open scoped TensorProduct
open GlobalTheory.LKInvGood
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localOrderTensorPadic_isAzumaya_almost_all : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] [Algebra.IsCentral F B] [IsSimpleRing B] [FiniteDimensional F B]
    (Λ : Subring B) (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ),
    Module.Finite ℤ Λ → (∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ Λ) →
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ N →
      letI := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ
      IsAzumaya (cenOrder ℓ F) (locOrder ℓ Λ) := by
  first | (exact @GlobalTheory.LocAzumaya.locOrder_isAzumaya) | (exact GlobalTheory.LocAzumaya.locOrder_isAzumaya) | (intros; apply GlobalTheory.LocAzumaya.locOrder_isAzumaya <;> assumption)
