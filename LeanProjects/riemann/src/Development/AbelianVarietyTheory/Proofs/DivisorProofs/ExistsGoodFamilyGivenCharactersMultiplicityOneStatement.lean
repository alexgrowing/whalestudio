import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodFamilyGivenCharactersMultiplicityOne
import Formalism.LocalToGlobal.IndefiniteReal.CxPass
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
open Formalism.L2.DIV NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_goodFamily_given_characters_multiplicityOne : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (X : Finset (G → K)), (∀ χ ∈ X, IsAbsIrrChar χ) → ∀ (P0 : Subgroup G) [Fintype P0] (ψ0 : P0 →* Kˣ), (∀ χ ∈ X, ∑ h : P0, χ (h : G) * (((ψ0 h)⁻¹ : Kˣ) : K) = (Fintype.card P0 : K)) → ∃ (S : Type) (_ : Fintype S) (Ws : S → Type) (_ : ∀ s, AddCommGroup (Ws s)) (_ : ∀ s, Module K (Ws s)) (_ : ∀ s, FiniteDimensional K (Ws s)) (τ : ∀ s, Representation K G (Ws s)), Formalism.IndefR.TransferLatticeStatement.IsGood τ ∧ (∀ χ : G → K, χ ∈ X ↔ ∃ s, Formalism.IndefR.TransferLatticeStatement.charOf (τ s) = χ) ∧ Formalism.IndefR.IndefiniteEpsilonOperator.M1 τ ⟨P0, ψ0⟩ := by
  first | exact @GlobalTheory.GoodFamilyOfChars.exists_goodFamily | exact GlobalTheory.GoodFamilyOfChars.exists_goodFamily | (intros; apply GlobalTheory.GoodFamilyOfChars.exists_goodFamily <;> assumption)
