import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LengthEqLengthInvariantsOfTorsionLevels
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.CardKill

open scoped TensorProduct
open GlobalTheory.TateLimit

theorem UpperTheory.V.K.cardRed :
    ∀ (l : ℕ) [Fact l.Prime] (K : Type) [AddCommGroup K] [Module ℤ_[l] K] [Finite K] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (W : Type) [AddCommGroup W] [Module ℤ_[l] W] (p : K →ₗ[ℤ_[l]] X) (h : K →ₗ[ℤ_[l]] W) (c : ℕ), Function.Surjective p → (∀ x, h x = 0 → (l : ℤ_[l]) ^ c • x = 0) → Nat.card X ≤ Nat.card (X ⧸ lpow l X 1) ^ c * Nat.card (LinearMap.range h) := by
  intro l _ K _ _ _ X _ _ W _ _ p h c hp hk
  haveI : Finite X := Finite.of_surjective p hp
  let Y : Submodule ℤ_[l] X := (LinearMap.ker h).map p
  have h1 : Nat.card Y ≤ Nat.card (X ⧸ lpow l X 1) ^ c := by
    refine UpperTheory.V.K.cardKill l X c Y ?_
    rintro y ⟨x, hx, rfl⟩
    rw [← map_smul, hk x hx, map_zero]
  have hle : LinearMap.ker h ≤ LinearMap.ker (Y.mkQ ∘ₗ p) := by
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact ⟨x, hx, rfl⟩
  haveI : Finite (K ⧸ LinearMap.ker h) := Finite.of_surjective _ (LinearMap.ker h).mkQ_surjective
  have h2 : Nat.card (X ⧸ Y) ≤ Nat.card (K ⧸ LinearMap.ker h) := by
    refine Nat.card_le_card_of_surjective ((LinearMap.ker h).liftQ (Y.mkQ ∘ₗ p) hle) fun z => ?_
    obtain ⟨x, rfl⟩ := (Y.mkQ_surjective.comp hp) z
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  have h4 : Nat.card (K ⧸ LinearMap.ker h) = Nat.card (LinearMap.range h) :=
    Nat.card_congr h.quotKerEquivRange.toEquiv
  rw [Submodule.card_eq_card_quotient_mul_card Y, ← h4]
  exact Nat.mul_le_mul h1 h2
