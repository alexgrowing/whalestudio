import Mathlib
import Formalism.LocalRingCardinality.DataLevel
import Formalism.LocalRingCardinality.DataLevelD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.OverPlaceIntegralForm
import Formalism.LogVandermondeBounds.LogVandermondeProofs.CardStabilizerVector
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory.Proof.StabilizerIndex

lemma index_field (F : Type) [Field F] [Finite F] (k : ℕ) (φ : Fin k → F) (hφ : φ ≠ 0) :
    (GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.stabRow φ).index = Nat.card F ^ k - 1 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have h := Formalism.LogVandermondeBounds.StandardLattice.cardStabilizerVector F k φ hφ
  have hcm := (GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.stabRow φ).card_mul_index
  have hc : Nat.card (GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.stabRow φ) =
      Nat.card {A : GL (Fin k) F // Matrix.vecMul φ (A : Matrix (Fin k) (Fin k) F) = φ} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun A => Iff.rfl))
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    ← hc, ← hcm] at h
  exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos h).symm

theorem index_stabRow : ∀ (κ : Type) [CommRing κ] (T k : ℕ), T.Prime → Nat.card κ = T →
    ∀ φ : Fin k → κ, φ ≠ 0 →
      (((GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.stabRow φ).index : ℕ) : ℝ) = (T : ℝ) ^ k - 1 := by
  intro κ _ T k hT hcard φ hφ
  haveI : Fact T.Prime := ⟨hT⟩
  haveI : Finite κ := Nat.finite_of_card_ne_zero (hcard ▸ hT.ne_zero)
  letI : Fintype κ := Fintype.ofFinite κ
  have e : ZMod T ≃+* κ := ZMod.ringEquivOfPrime κ hT (by rw [← Nat.card_eq_fintype_card, hcard])
  have hF : IsField κ := MulEquiv.isField (Field.toIsField (ZMod T)) e.symm.toMulEquiv
  have h := @index_field κ hF.toField _ k φ hφ
  have h' : (GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.stabRow φ).index = T ^ k - 1 := by
    rw [← hcard]; exact h
  rw [h', Nat.cast_sub (Nat.one_le_pow _ _ hT.pos)]
  push_cast
  rfl

end GlobalTheory.Proof.StabilizerIndex
