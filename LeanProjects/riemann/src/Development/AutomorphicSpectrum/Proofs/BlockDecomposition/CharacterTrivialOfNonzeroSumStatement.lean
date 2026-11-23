import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterTrivialOfNonzeroSum
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_trivial_of_nonzero_sum : ∀ {A : Type} [AddCommGroup A] (T large₂ : AddSubgroup A) (R : Finset A) (χ : A → ℂ),
  (∀ a ∈ T, ∀ b ∈ T, χ (a + b) = χ a * χ b) → (∀ l ∈ large₂, l ∈ T ∧ χ l = 1) → (∀ r ∈ R, r ∈ T) →
  (∀ m ∈ T, ∃! r, r ∈ R ∧ ∃ l ∈ large₂, m = r + l) → (∑ r ∈ R, χ r) ≠ 0 → ∀ m ∈ T, χ m = 1 := by
  first | exact @GlobalTheory.CompanionTheory.FiniteQuotientCharacter.eq_one_of_sum_representatives_ne_zero | exact GlobalTheory.CompanionTheory.FiniteQuotientCharacter.eq_one_of_sum_representatives_ne_zero | (intros; apply GlobalTheory.CompanionTheory.FiniteQuotientCharacter.eq_one_of_sum_representatives_ne_zero <;> assumption)
