import Mathlib
import GroundTheory.PAdicHodge.ACrisBdR
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open _root_.WittVector

namespace ACris

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]

local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)

theorem mem_acrisZero_of_forall_dvd {z : 𝔸}
    (h : ∀ m : ℕ, ∃ s ∈ ACrisZero K p, algebraMap (AInf K p) 𝔸 (xiGen K p ^ m) ∣ z - s) :
    z ∈ ACrisZero K p := by
  obtain ⟨N, w, hwN⟩ := IsLocalization.Away.surj (p : AInf K p) z
  rw [map_natCast] at hwN
  set m := p ^ N with hm
  have hm0 : m ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  obtain ⟨s, hs, r, hr⟩ := h m
  obtain ⟨s', hs', w', r', hw', hr'⟩ := exists_decomp ker_eq_span_xiGen m hs
  set ξm := algebraMap (AInf K p) 𝔸 (xiGen K p ^ m)
  have hz : z = s' + ξm * (r + r') := by
    rw [show z = s + (z - s) by ring, hr, hr']; ring
  have hfac : ((m.factorial : ℕ) : 𝔸) = (p : 𝔸) ^ N * ((m - 1).factorial : 𝔸) := by
    rw [← Nat.mul_factorial_pred hm0, Nat.cast_mul, hm, Nat.cast_pow]

  have hW : ξm * ((m.factorial : 𝔸) * (r + r')) =
      algebraMap (AInf K p) 𝔸 (((m - 1).factorial : AInf K p) * w - (p : AInf K p) ^ N * w') := by
    have e1 : ξm * (r + r') = z - s' := by rw [hz]; ring
    rw [map_sub, map_mul, map_mul, map_pow, map_natCast, map_natCast, ← hw', ← hwN, hfac]
    linear_combination ((p : 𝔸) ^ N * ((m - 1).factorial : 𝔸)) * e1
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 ((algebraMap_dvd_iff m _).1 ⟨_, hW.symm⟩)
  have hnz : xiGen K p ^ m ∈ nonZeroDivisors (AInf K p) :=
    pow_mem (IsPerfectoidField.mem_nonZeroDivisors_of_ker_eq_span ker_eq_span_xiGen) m
  have hR : (m.factorial : 𝔸) * (r + r') = algebraMap (AInf K p) 𝔸 d := by
    have h0 : algebraMap (AInf K p) 𝔸 (xiGen K p ^ m) * ((m.factorial : 𝔸) * (r + r') -
        algebraMap (AInf K p) 𝔸 d) = 0 := by
      rw [mul_sub, hW, ← map_mul, ← hd, mul_comm, sub_self]
    exact sub_eq_zero.1 (eq_zero_of_algebraMap_mul_eq_zero hnz h0)
  have hxi : ξm * (r + r') = dpow m (xiGen K p) * algebraMap (AInf K p) 𝔸 d := by
    rw [← hR, ← mul_assoc, mul_comm (dpow m (xiGen K p)), factorial_mul_dpow, ← map_pow]
  have hξmem : xiGen K p ∈ RingHom.ker θ := by
    rw [ker_eq_span_xiGen]; exact Ideal.mem_span_singleton_self _
  rw [hz, hxi]
  exact add_mem hs' (Subalgebra.mul_mem _ (dpow_mem hξmem m) (Subalgebra.algebraMap_mem _ d))

theorem iotaM_eq_zero {y : ACris K p} (hy : iota K p y = 0) (m : ℕ) : embedding₂ K p m y = 0 := by
  have h := evalₐ_iota (K := K) (p := p) m y
  have h0 : @Eq (_root_.AdicCompletion (kerAway K p) 𝔸) (iota K p y) 0 := hy
  rw [h0, map_zero] at h
  exact Subtype.ext h.symm

theorem span_p_pow_map (k : ℕ) :
    (Ideal.span {(p : ACrisZero K p)} ^ k).map (algebraMap (ACrisZero K p) (ACris K p)) =
      Ideal.span {(p : ACris K p)} ^ k := by
  rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast]

set_option maxHeartbeats 1600000 in

theorem exists_eq_pow_mul_of_iota_eq_zero {y : ACris K p} (hy : iota K p y = 0) {k : ℕ}
    {yk : ACrisZero K p}
    (ha : y - _root_.AdicCompletion.of _ _ yk ∈
      (Ideal.span {(p : ACrisZero K p)} ^ k).map (algebraMap (ACrisZero K p) (ACris K p))) :
    ∃ z ∈ ACrisZero K p, (yk : 𝔸) = (p : 𝔸) ^ k * z := by
  have hu := isUnit_natCast (K := K) (p := p) hp.out.ne_zero
  refine ⟨↑(hu.unit⁻¹ ^ k) * (yk : 𝔸), ?_, ?_⟩
  · refine mem_acrisZero_of_forall_dvd fun m => ?_

    have h1 : embedding₂ K p m (y - _root_.AdicCompletion.of _ _ yk) ∈ Ideal.span {(p : acrisQ K p m)} ^ k := by
      have hle : (Ideal.span {(p : ACrisZero K p)} ^ k).map
          ((embedding₂ K p m).comp (algebraMap (ACrisZero K p) (ACris K p))) ≤
          Ideal.span {(p : acrisQ K p m)} ^ k := by
        rw [Ideal.map_le_iff_le_comap]
        refine (Ideal.pow_right_mono ?_ k).trans (Ideal.le_comap_pow _ k)
        rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
        exact Ideal.mem_span_singleton_self _
      apply hle
      rw [← Ideal.map_map]
      exact Ideal.mem_map_of_mem _ ha
    rw [map_sub, iotaM_eq_zero hy, zero_sub, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
    obtain ⟨t, ht⟩ := h1
    obtain ⟨s, hs, hst⟩ := t.2
    have h3 := congrArg (fun x : acrisQ K p m => (x : 𝔸 ⧸ kerAway K p ^ m)) ht
    simp only [NegMemClass.coe_neg, SubringClass.coe_natCast, SubmonoidClass.coe_pow,
      MulMemClass.coe_mul] at h3
    rw [embedding₂, AdicCompletion.extendRingHom_of, coe_iotaZero, ← hst] at h3
    refine ⟨-s, neg_mem hs, ?_⟩
    have h4 : Ideal.Quotient.mk (kerAway K p ^ m) ((yk : 𝔸) - (p : 𝔸) ^ k * (-s)) = 0 := by
      rw [map_sub, map_mul, map_pow, map_natCast, map_neg, mul_neg, sub_neg_eq_add, ← h3,
        add_neg_cancel]
    rw [mk_eq_zero_iff] at h4
    have h5 : (yk : 𝔸) - (p : 𝔸) ^ k * (-s) =
        (p : 𝔸) ^ k * (↑(hu.unit⁻¹ ^ k) * (yk : 𝔸) - -s) := by
      rw [mul_sub, ← mul_assoc, Units.val_pow_eq_pow_val, ← mul_pow, IsUnit.mul_val_inv, one_pow,
        one_mul]
    rw [h5] at h4
    exact ((hu.pow k).dvd_mul_left).1 h4
  · rw [← mul_assoc, Units.val_pow_eq_pow_val, ← mul_pow, IsUnit.mul_val_inv, one_pow, one_mul]

set_option maxHeartbeats 1600000 in

theorem iota_injective : Function.Injective (iota K p) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  refine IsHausdorff.haus' (I := Ideal.span {(p : ACris K p)}) y fun k => ?_
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top, ← span_p_pow_map]

  obtain ⟨yk, hyk⟩ := Ideal.Quotient.mk_surjective
    (_root_.AdicCompletion.evalₐ (Ideal.span {(p : ACrisZero K p)}) k y)
  have hker : y - _root_.AdicCompletion.of _ _ yk ∈
      (Ideal.span {(p : ACrisZero K p)} ^ k).map
        (algebraMap (ACrisZero K p) (ACris K p)) := by
    rw [← ker_adicCompletion_evalₐ (Submodule.fg_span_singleton _), RingHom.mem_ker]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub]
    rw [← hyk]
    exact sub_eq_zero.2 (_root_.AdicCompletion.evalₐ_of _ k yk).symm
  obtain ⟨z, hz, hzk⟩ := exists_eq_pow_mul_of_iota_eq_zero hy hker
  have hyk' : yk ∈ Ideal.span {(p : ACrisZero K p)} ^ k := by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨⟨z, hz⟩, Subtype.ext (by simpa using hzk)⟩
  have := add_mem hker (Ideal.mem_map_of_mem (algebraMap (ACrisZero K p) (ACris K p)) hyk')
  rwa [show (algebraMap (ACrisZero K p) (ACris K p)) yk = _root_.AdicCompletion.of _ _ yk from rfl,
    sub_add_cancel] at this

end ACris

end GroundTheory.PAdicHodge
