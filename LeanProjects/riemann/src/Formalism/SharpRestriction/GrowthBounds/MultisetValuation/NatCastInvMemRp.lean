import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.InClassOfExp

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Pi

variable (p : ℕ) [hp : Fact p.Prime] (K' : Type) [Field K'] [Algebra (K0 p) K']

theorem pK'_ne : ((p : ℕ) : K') ≠ 0 := by
  intro h
  apply WittVector.FractionRing.p_nonzero p (kb p)
  apply (algebraMap (K0 p) K').injective
  rw [map_natCast, h, map_zero]

theorem W_mem_Rp (vp : K') (x : WW p) : algebraMap (K0 p) K' (algebraMap (WW p) (K0 p) x) ∈ Rp p K' vp :=
  Subring.subset_closure (Set.mem_union_left _ ⟨x, rfl⟩)

theorem vp_mem_Rp (vp : K') : vp ∈ Rp p K' vp :=
  Subring.subset_closure (Set.mem_union_right _ (Set.mem_singleton vp))

theorem natCast_unit (m : ℕ) (hm : ¬ p ∣ m) :
    ∃ w : WW p, (m : K') * algebraMap (K0 p) K' (algebraMap (WW p) (K0 p) w) = 1 := by
  have h := map_natCast (WittVector.constantCoeff (p := p) (R := kb p)) m
  have h' : ((m : WW p)).coeff 0 = (m : kb p) := h
  have hc : ((m : WW p)).coeff 0 ≠ 0 := by
    rw [h']
    exact (CharP.cast_eq_zero_iff (kb p) p m).not.mpr hm
  have hu : IsUnit (m : WW p) := WittVector.isUnit_of_coeff_zero_ne_zero (p := p) _ hc
  refine ⟨↑hu.unit⁻¹, ?_⟩
  rw [← map_natCast (algebraMap (K0 p) K') m, ← map_natCast (algebraMap (WW p) (K0 p)) m, ← map_mul,
    ← map_mul, hu.mul_val_inv, map_one, map_one]

theorem natCast_inv_mem_Rp (vp : K') (m : ℕ) (hm : ¬ p ∣ m) : ((m : K'))⁻¹ ∈ Rp p K' vp := by
  obtain ⟨w, hw⟩ := natCast_unit p K' m hm
  rw [inv_eq_of_mul_eq_one_right hw]
  exact W_mem_Rp p K' vp w

private lemma exists_not_dvd_eq_pow_padicValNat_mul (n : ℕ) (hn : n ≠ 0) : ∃ m, ¬ p ∣ m ∧ n = p ^ padicValNat p n * m := by
  obtain ⟨m, hm⟩ := (pow_padicValNat_dvd : p ^ padicValNat p n ∣ n)
  refine ⟨m, fun ⟨c, hc⟩ => pow_succ_padicValNat_not_dvd (p := p) hn ⟨c, ?_⟩, hm⟩
  conv_lhs => rw [hm]
  rw [hc]
  ring

theorem piFact (vp : K') (hvp : vp ^ (p ^ 2 - 1) = (p : K')) (k : ℕ) :
    (vp ^ (p + 1)) ^ k * ((k.factorial : K'))⁻¹ ∈ Rp p K' vp := by
  have hle : (p - 1) * padicValNat p k.factorial ≤ k := by
    rw [sub_one_mul_padicValNat_factorial]
    exact Nat.sub_le _ _
  obtain ⟨m, hmp, hm⟩ := exists_not_dvd_eq_pow_padicValNat_mul p k.factorial (Nat.factorial_ne_zero k)
  generalize padicValNat p k.factorial = v at hle hm
  obtain ⟨r, hr⟩ : ∃ r, k = (p - 1) * v + r := ⟨k - (p - 1) * v, by omega⟩
  have hp0 : ((p : K')) ≠ 0 := pK'_ne p K'
  have e : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    have h1 := hp.out.one_le
    have h2 : 1 ≤ p ^ 2 := Nat.one_le_pow 2 p hp.out.pos
    zify [h1, h2]
    ring
  have hpow : (vp ^ (p + 1)) ^ ((p - 1) * v + r) = (p : K') ^ v * vp ^ ((p + 1) * r) := by
    rw [← pow_mul, mul_add, pow_add, ← mul_assoc, ← e, pow_mul vp (p ^ 2 - 1) v, hvp]
  rw [hm, Nat.cast_mul, Nat.cast_pow, hr, hpow, mul_inv, mul_comm ((p : K') ^ v), mul_assoc,
    ← mul_assoc ((p : K') ^ v), mul_inv_cancel₀ (pow_ne_zero _ hp0), one_mul]
  exact Subring.mul_mem _ (Subring.pow_mem _ (vp_mem_Rp p K' vp) _) (natCast_inv_mem_Rp p K' vp m hmp)

end Pi

theorem charZero_K' (p : ℕ) [hp : Fact p.Prime] (K' : Type) [Field K'] [Algebra (K0 p) K'] : CharZero K' := by
  refine charZero_of_inj_zero fun n hn => ?_
  by_contra h0
  obtain ⟨m, hmp, hm⟩ := exists_not_dvd_eq_pow_padicValNat_mul p n h0
  obtain ⟨w, hw⟩ := natCast_unit p K' m hmp
  rw [hm, Nat.cast_mul, Nat.cast_pow] at hn
  have h1 : ((p : K') ^ padicValNat p n * (m : K')) * algebraMap (K0 p) K' (algebraMap (WW p) (K0 p) w) =
      (p : K') ^ padicValNat p n := by
    rw [mul_assoc, hw, mul_one]
  rw [hn, zero_mul] at h1
  exact pow_ne_zero _ (pK'_ne p K') h1.symm

end Formalism.MainNotions.FormalGroupSystem.Pf
