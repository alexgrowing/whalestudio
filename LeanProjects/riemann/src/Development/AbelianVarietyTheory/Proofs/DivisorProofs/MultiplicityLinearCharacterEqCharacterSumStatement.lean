import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityLinearCharacterEqCharacterSum
import Formalism.LocalToGlobal.IndefiniteReal.CxPass
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
open Formalism.L2.DIV NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicity_linearCharacter_eq_characterSum : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (τ : Representation K G W) (H : Subgroup G) [Fintype H] (ψ : H →* Kˣ), (Formalism.IndefR.IndefiniteEpsilonOperator.nOf τ ⟨H, ψ⟩ : K) = (Nat.card H : K)⁻¹ * ∑ h : H, Formalism.IndefR.TransferLatticeStatement.charOf τ (h : G) * (((ψ h)⁻¹ : Kˣ) : K) := by
  first | exact @GlobalTheory.multiplicity_linearCharacter_eq_characterSum.nOf_eq_charSum | exact GlobalTheory.multiplicity_linearCharacter_eq_characterSum.nOf_eq_charSum | (intros; apply GlobalTheory.multiplicity_linearCharacter_eq_characterSum.nOf_eq_charSum <;> assumption)
