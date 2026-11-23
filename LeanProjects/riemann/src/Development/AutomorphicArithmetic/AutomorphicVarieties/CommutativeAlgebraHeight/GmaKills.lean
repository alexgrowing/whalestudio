import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DCorner
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DkerOfKills

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.gma_kills :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (e : Fin n → E), 1 ≤ n → IsGMA D e → ∀ x, x ∈ D.ker ↔ ∀ y, D.tr (y * x) = 0 := by
  intro n A E _ _ _ D e hn hG x
  refine ⟨fun hx y => (d_ker D x).2.2 hx y 1 le_rfl hn, fun hx => ?_⟩
  have hj : ∀ j, x * e j ∈ D.ker := by
    intro j
    refine (d_ker D _).1.2 fun S _ _ h => ?_
    have hz : ∀ y, e j * (y * x) * e j = 0 := fun y => by
      rw [(d_corner D (e j) hG.ch (hG.idem.idem j) (hG.rank j) hn).1, ← mul_assoc, hx, zero_smul]
    have h0 : ∀ w : S ⊗[A] E, ((1 : S) ⊗ₜ[A] e j) * (w * ((1 : S) ⊗ₜ[A] (x * e j))) = 0 := by
      intro w
      induction w with
      | zero => simp
      | tmul s y =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, ← mul_assoc y,
          ← mul_assoc (e j), hz, tmul_zero]
      | add a b ha hb => rw [add_mul, mul_add, ha, hb, add_zero]
    have h1 : h * ((1 : S) ⊗ₜ[A] (x * e j)) = (h * ((1 : S) ⊗ₜ[A] (x * e j))) * ((1 : S) ⊗ₜ[A] e j) := by
      rw [mul_assoc h, Algebra.TensorProduct.tmul_mul_tmul, mul_assoc x, (hG.idem.idem j).eq, one_mul]
    rw [h1, d_comm, h0, add_zero, map_one]
  have : x = ∑ j, x * e j := by rw [← Finset.mul_sum, hG.idem.complete, mul_one]
  rw [this]
  exact sum_mem fun j _ => hj j
