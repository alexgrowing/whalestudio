import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisCocycleIntegralAfterScaling
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_cocycle_integral_after_scaling : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (S : Finset Pl) (W : R2 Ω l) (c : Coef l) (z : G ℚ Ω → Fin 2 → Qbar l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ W.ker) → z ∈ Z1 (Loc.colRep W) → Unr W z → ∀ A : ValuationSubring Ω, ∃ (c' : Coef l) (k : ℕ), c.O ≤ c'.O ∧ (∀ s i, ((l : ℕ) : Qbar l) ^ k * z s i ∈ c'.O) ∧ (∀ q : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∃ x : Fin 2 → Qbar l, (∀ i, x i ∈ c'.O) ∧ ∀ s ∈ Ine (F := ℚ) B, ((l : ℕ) : Qbar l) ^ k • z s = mat W s *ᵥ x - x) ∧ (Triv W A z → ∃ x : Fin 2 → Qbar l, (∀ i, x i ∈ c'.O) ∧ ∀ s ∈ Dec (F := ℚ) A, ((l : ℕ) : Qbar l) ^ k • z s = mat W s *ᵥ x - x) ∧ (Gr W A z → ∃ x ∈ c'.O, ∀ s ∈ Dec (F := ℚ) A, ((l : ℕ) : Qbar l) ^ k * z s 1 = mat W s 1 1 * x - x) := by
  first | exact @GlobalTheory.CocInt.integral_after_scaling | exact GlobalTheory.CocInt.integral_after_scaling | (intros; apply GlobalTheory.CocInt.integral_after_scaling <;> assumption)
