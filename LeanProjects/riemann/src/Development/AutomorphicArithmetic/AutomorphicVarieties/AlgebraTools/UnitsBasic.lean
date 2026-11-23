import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InvAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.EqLagIff

open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

private theorem units_x_mul_ep_and_st_idempotent_identities {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) {ι : Type} [Fintype ι] [DecidableEq ι] (o : ι → ι) (U : T.Units ι o) (i : ι) :
    U.x i * U.ep i = U.x i ∧ U.ep (o i) * U.x i = U.x i ∧ T.st (U.x i) * U.ep (o i) = T.st (U.x i) ∧ U.ep i * T.st (U.x i) = T.st (U.x i) := by
  have hr : U.x i * U.ep i = U.x i := by
    conv_rhs => rw [← U.x_mem i]
    conv_lhs => rw [← U.x_mem i]
    rw [mul_assoc _ (U.ep i) (U.ep i), (U.coi.idem i).eq]
  have hl : U.ep (o i) * U.x i = U.x i := by
    conv_rhs => rw [← U.x_mem i]
    conv_lhs => rw [← U.x_mem i]
    simp only [← mul_assoc, (U.coi.idem (o i)).eq]
  refine ⟨hr, hl, ?_, ?_⟩
  · have h := congrArg T.st hl
    rwa [T.st_mul, U.st_ep] at h
  · have h := congrArg T.st hr
    rwa [T.st_mul, U.st_ep] at h

theorem UpperTheory.V.AlgebraTools.units_basic :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) {ι : Type} [Fintype ι] [DecidableEq ι] (o : ι → ι) (U : T.Units ι o), (∀ i j, i ≠ j → U.x i * T.st (U.x j) = 0) ∧ ∑ i, T.st (U.x i) * U.x i = 1 ∧ (∀ i j y, i ≠ j → T.tr (U.ep i * y * U.ep j) = 0) ∧ (∀ y, T.tr y = ∑ i, T.tr (U.x i * y * T.st (U.x i))) ∧ (∀ i j y, o i = o j → U.x i * y * T.st (U.x j) = T.tr (U.x i * y * T.st (U.x j)) • U.ep (o i)) ∧ (∀ y, y = ∑ i, ∑ j, T.st (U.x i) * (U.x i * y * T.st (U.x j)) * U.x j) ∧ ∀ i j y, U.ep (o i) * (U.x i * y * T.st (U.x j)) * U.ep (o j) = U.x i * y * T.st (U.x j) := by
  intro B E _ _ _ T ι _ _ o U
  have key : ∀ i j y, U.ep (o i) * (U.x i * y * T.st (U.x j)) * U.ep (o j) = U.x i * y * T.st (U.x j) := by
    intro i j y
    obtain ⟨-, hl, hs, -⟩ := units_x_mul_ep_and_st_idempotent_identities T o U i
    obtain ⟨-, -, hs', -⟩ := units_x_mul_ep_and_st_idempotent_identities T o U j
    simp only [← mul_assoc]
    rw [hl, mul_assoc _ (T.st (U.x j)), hs']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, key⟩
  · intro i j h
    obtain ⟨hr, -, -, -⟩ := units_x_mul_ep_and_st_idempotent_identities T o U i
    obtain ⟨-, -, -, hs⟩ := units_x_mul_ep_and_st_idempotent_identities T o U j
    rw [← hr, ← hs, mul_assoc, ← mul_assoc (U.ep i), U.coi.ortho h, zero_mul, mul_zero]
  · simp_rw [U.st_mul_x_eq]
    exact U.coi.complete
  · intro i j y h
    rw [T.tr_comm, ← mul_assoc, U.coi.ortho (Ne.symm h), zero_mul, map_zero]
  · intro y
    have h : ∀ i, T.tr (U.x i * y * T.st (U.x i)) = T.tr (U.ep i * y) := by
      intro i
      rw [T.tr_comm, ← mul_assoc, U.st_mul_x_eq]
    simp_rw [h]
    rw [← map_sum, ← Finset.sum_mul, U.coi.complete, one_mul]
  · intro i j y h
    have h7 := key i j y
    rw [← h] at h7
    calc U.x i * y * T.st (U.x j)
        = U.ep (o i) * (U.x i * y * T.st (U.x j)) * U.ep (o i) := h7.symm
      _ = T.tr (U.ep (o i) * (U.x i * y * T.st (U.x j)) * U.ep (o i)) • U.ep (o i) := U.corner_eq _ _
      _ = T.tr (U.x i * y * T.st (U.x j)) • U.ep (o i) := by rw [h7]
  · intro y
    have h : ∀ i j, T.st (U.x i) * (U.x i * y * T.st (U.x j)) * U.x j = U.ep i * y * U.ep j := by
      intro i j
      rw [← U.st_mul_x_eq i, ← U.st_mul_x_eq j]
      simp only [mul_assoc]
    simp_rw [h, ← Finset.mul_sum, ← Finset.sum_mul, U.coi.complete, mul_one, one_mul]
