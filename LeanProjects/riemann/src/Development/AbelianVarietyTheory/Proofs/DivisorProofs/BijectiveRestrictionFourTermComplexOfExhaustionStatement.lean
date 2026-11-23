import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveRestrictionFourTermComplexOfExhaustion
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
open CategoryTheory GlobalTheory.CxCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_restriction_fourTermComplex_of_exhaustion : ∀ (C : Type 1) [Category.{0} C] (D : Type) [Category.{0} D] (K : Cx C) (P : ℕ → ObjectProperty C) (ℓ : D ⥤ C) (N₀ : ℕ), (∀ m n T, m ≤ n → P m T → P n T) → (∀ T, ∃ n, P n T) → (∀ N, N₀ ≤ N → ∃ h : ∀ U, P N (ℓ.obj U), ((K.res (P N).ι).resMap ((P N).lift ℓ h)).Bij) → Function.Bijective (K.resMap ℓ).h2 := by
  first | exact @GlobalTheory.CxTowerTwo.tower_two | exact GlobalTheory.CxTowerTwo.tower_two | (intros; apply GlobalTheory.CxTowerTwo.tower_two <;> assumption)
