import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.GcNeg

open UpperTheory.V.FW

private theorem coeff_thetaH (M c : ℕ) [NeZero M] (s : (ZMod M)ˣ) :
    (thetaH M c).coeff s = if 2 * (s : ZMod M).val < M then gc M c s else 0 := by
  classical
  simp [thetaH, Finsupp.single_apply, Finset.sum_ite_eq']

private theorem coeff_mul_J (M : ℕ) [NeZero M] (f : MonoidAlgebra ℤ (ZMod M)ˣ) (s : (ZMod M)ˣ) :
    (f * MonoidAlgebra.of ℤ _ (-1 : (ZMod M)ˣ)).coeff s = f.coeff (-s) := by
  rw [show MonoidAlgebra.of ℤ _ (-1 : (ZMod M)ˣ) = MonoidAlgebra.single (-1) 1 from rfl]
  rw [MonoidAlgebra.coeff_mul_single_eq_coeff_mul (-s), mul_one]
  intro m _
  rw [mul_neg_one, neg_eq_iff_eq_neg]

private theorem half (M : ℕ) [NeZero M] (hM : 2 < M) (s : (ZMod M)ˣ) :
    (s : ZMod M) ≠ 0 ∧ (2 * (-(s : ZMod M)).val < M ↔ ¬ 2 * (s : ZMod M).val < M) := by
  have hs0 : (s : ZMod M) ≠ 0 := by
    haveI : Fact (1 < M) := ⟨by omega⟩
    exact s.ne_zero
  refine ⟨hs0, ?_⟩
  rw [ZMod.neg_val, if_neg hs0]
  have hlt := ZMod.val_lt (s : ZMod M)
  have hne : 2 * (s : ZMod M).val ≠ M := by
    intro h
    have h2 : (2 : ZMod M) * (s : ZMod M) = 0 := by
      have : ((2 * (s : ZMod M).val : ℕ) : ZMod M) = 0 := by
        rw [h]
        exact ZMod.natCast_self M
      push_cast at this
      rwa [ZMod.natCast_zmod_val] at this
    have h3 : (2 : ZMod M) = 0 := by
      have := congrArg (· * ((s⁻¹ : (ZMod M)ˣ) : ZMod M)) h2
      simpa [mul_assoc] using this
    have h4 : ((2 : ℕ) : ZMod M) = 0 := by exact_mod_cast h3
    rw [ZMod.natCast_eq_zero_iff] at h4
    have := Nat.le_of_dvd (by norm_num) h4
    omega
  omega

theorem UpperTheory.V.FW.thetaFull :
    ∀ (M c : ℕ) [NeZero M], c.Coprime M → Odd c → 2 < M → thetaH M c * (1 - MonoidAlgebra.of ℤ _ (-1 : (ZMod M)ˣ)) = ∑ s : (ZMod M)ˣ, MonoidAlgebra.single s (gc M c s) ∧ ∀ s : (ZMod M)ˣ, (((thetaH M c * (1 + MonoidAlgebra.of ℤ _ (-1 : (ZMod M)ˣ))).coeff s : ℤ) : ZMod 2) = (gc M c s : ZMod 2) := by
  intro M c _ hc hodd hM
  have key : ∀ s : (ZMod M)ˣ, (thetaH M c).coeff (-s) = if 2 * (s : ZMod M).val < M then 0 else -gc M c s := by
    intro s
    obtain ⟨hs0, hiff⟩ := half M hM s
    rw [coeff_thetaH, Units.val_neg]
    by_cases h : 2 * (s : ZMod M).val < M
    · rw [if_neg (fun h' => hiff.mp h' h), if_pos h]
    · rw [if_pos (hiff.mpr h), if_neg h, gcNeg M c _ hc hodd hs0]
  constructor
  · rw [mul_sub, mul_one, sub_eq_iff_eq_add]
    refine MonoidAlgebra.ext (Finsupp.ext fun s => ?_)
    rw [MonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_mul_J, key, coeff_thetaH]
    classical
    simp only [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.finset_sum_apply, Finsupp.single_apply, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    split_ifs <;> simp
  · intro s
    rw [mul_add, mul_one, MonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_mul_J, key, coeff_thetaH]
    split_ifs
    · simp
    · push_cast
      simp [ZMod.neg_eq_self_mod_two]
