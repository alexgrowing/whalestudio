import Mathlib
import GroundTheory.PAdicHodge.ThetaPlus
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Ideal WittVector IsLocalRing

section Binomial

variable {A : Type*} [CommRing A]

theorem one_add_pow_prime_pow_sub_one_mem {p : ℕ} (hp : p.Prime) (y : A) (N r k : ℕ)
    (hk : k ≤ p ^ r) :
    (1 + y) ^ (p ^ N) - 1 ∈ span {(p : A) ^ (N - r)} ⊔ span {y ^ k} := by
  rw [add_comm, add_pow, Finset.sum_range_succ']
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, add_sub_cancel_right]
  refine Ideal.sum_mem _ fun j hj => ?_
  by_cases hjk : k ≤ j + 1
  · exact Ideal.mem_sup_right (mul_mem_right _ _ (mem_span_singleton.2 (pow_dvd_pow y hjk)))
  · apply Ideal.mem_sup_left
    have hj' : j + 1 ≤ p ^ N := Finset.mem_range.1 hj
    have h1 : (j + 1).factorization p < r := by
      have h2 : p ^ (j + 1).factorization p ≤ j + 1 :=
        Nat.le_of_dvd (Nat.succ_pos j) (Nat.ordProj_dvd (j + 1) p)
      exact (Nat.pow_lt_pow_iff_right hp.one_lt).1 (lt_of_le_of_lt h2 (by omega))
    have h3 : p ^ (N - r) ∣ Nat.choose (p ^ N) (j + 1) := by
      have h4 := Nat.factorization_choose_prime_pow hp hj' (Nat.succ_ne_zero j)
      refine (Nat.pow_dvd_pow p (by omega : N - r ≤ N - (j + 1).factorization p)).trans ?_
      rw [← h4]
      exact Nat.ordProj_dvd _ p
    refine mul_mem_left _ _ (mem_span_singleton.2 ?_)
    exact_mod_cast Nat.cast_dvd_cast (α := A) h3

end Binomial

namespace IsPerfectoidField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [CharZero K]

local notation "𝒪" => normInteger K
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger K) p)
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔹" => BDeRhamPlus (normInteger K) p
local notation "𝔸" => Localization.Away (p : WittVector p (PreTilt (normInteger K) p))

omit [CharZero K] in

theorem eq_zero_of_forall_mem_span_p_pow {b : 𝒪} (h : ∀ M : ℕ, b ∈ span {(p : 𝒪) ^ M}) : b = 0 := by
  have := isAdicComplete (K := K) p
  refine IsHausdorff.haus (I := span {(p : 𝒪)}) inferInstance _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, mul_top, span_singleton_pow]
  exact h n

omit [IsPerfectoidField K p] in

theorem natCast_p_ne_zero : (p : 𝒪) ≠ 0 := by
  intro h
  have h2 : ((p : 𝒪) : K) = 0 := by rw [h]; rfl
  rw [Subring.coe_natCast] at h2
  exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) h2

variable {ξ : WittVector p (PreTilt (normInteger K) p)}

theorem mem_span_xi_pow_of_p_pow_mul_mem (hξ : RingHom.ker θ = span {ξ}) {x : 𝕎𝒪♭} {s k : ℕ}
    (h : (p : 𝕎𝒪♭) ^ s * x ∈ span {ξ ^ k}) : x ∈ span {ξ ^ k} := by
  have hnz := mem_nonZeroDivisors_of_ker_eq_span hξ
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have hx1 : (p : 𝕎𝒪♭) ^ s * x ∈ RingHom.ker θ := by
      rw [hξ]
      exact (Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self ξ (Nat.succ_ne_zero k))) h
    have hx2 : x ∈ RingHom.ker θ := by
      rw [RingHom.mem_ker, map_mul, map_pow, map_natCast] at hx1
      rw [RingHom.mem_ker]
      exact (mul_eq_zero.1 hx1).resolve_left (pow_ne_zero _ natCast_p_ne_zero)
    rw [hξ, mem_span_singleton] at hx2
    obtain ⟨x', rfl⟩ := hx2
    obtain ⟨c, hc⟩ := mem_span_singleton.1 h
    have h3 : (p : 𝕎𝒪♭) ^ s * x' = ξ ^ k * c := by
      have h4 : ξ * ((p : 𝕎𝒪♭) ^ s * x' - ξ ^ k * c) = 0 := by
        rw [pow_succ] at hc
        linear_combination hc
      exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff.1 hnz).1 _ h4)
    have h5 := ih (mem_span_singleton.2 ⟨c, h3⟩)
    obtain ⟨d, hd⟩ := mem_span_singleton.1 h5
    exact mem_span_singleton.2 ⟨d, by rw [hd, pow_succ]; ring⟩

theorem mem_span_xi_pow_of_forall_mem_sup (hξ : RingHom.ker θ = span {ξ}) {x : 𝕎𝒪♭} {k : ℕ}
    (h : ∀ M : ℕ, x ∈ span {(p : 𝕎𝒪♭) ^ M} ⊔ span {ξ ^ k}) : x ∈ span {ξ ^ k} := by
  have hnz := mem_nonZeroDivisors_of_ker_eq_span hξ
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have hθ : θ x = 0 := by
      refine eq_zero_of_forall_mem_span_p_pow (p := p) fun M => ?_
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (h M)
      obtain ⟨a', rfl⟩ := mem_span_singleton.1 ha
      obtain ⟨b', rfl⟩ := mem_span_singleton.1 hb
      have hξ0 : θ ξ = 0 := by
        rw [← RingHom.mem_ker, hξ]; exact mem_span_singleton_self ξ
      rw [← hab, map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, hξ0,
        zero_pow (Nat.succ_ne_zero k), zero_mul, add_zero]
      exact mem_span_singleton.2 ⟨_, rfl⟩
    have hx2 : x ∈ span {ξ} := by rw [← hξ]; exact hθ
    obtain ⟨x', rfl⟩ := mem_span_singleton.1 hx2
    have h' : ∀ M : ℕ, x' ∈ span {(p : 𝕎𝒪♭) ^ M} ⊔ span {ξ ^ k} := by
      intro M
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (h M)
      obtain ⟨a', rfl⟩ := mem_span_singleton.1 ha
      obtain ⟨b', rfl⟩ := mem_span_singleton.1 hb
      have ha1 : (p : 𝕎𝒪♭) ^ M * a' ∈ span {ξ ^ 1} := by
        rw [pow_one, mem_span_singleton]
        exact ⟨x' - ξ ^ k * b', by rw [← sub_eq_iff_eq_add.2 hab.symm, pow_succ]; ring⟩
      obtain ⟨a'', ha''⟩ := mem_span_singleton.1 (mem_span_xi_pow_of_p_pow_mul_mem hξ ha1)
      have h4 : ξ * (x' - (p : 𝕎𝒪♭) ^ M * a'' - ξ ^ k * b') = 0 := by
        rw [pow_one] at ha''
        rw [ha'', pow_succ] at hab
        linear_combination -hab
      have h5 := sub_eq_zero.1 ((mem_nonZeroDivisors_iff.1 hnz).1 _ h4)
      refine Submodule.mem_sup.2 ⟨_, mem_span_singleton.2 ⟨a'', rfl⟩, _,
        mem_span_singleton.2 ⟨b', rfl⟩, ?_⟩
      rw [← h5]; ring
    obtain ⟨d, hd⟩ := mem_span_singleton.1 (ih h')
    exact mem_span_singleton.2 ⟨d, by rw [hd, pow_succ]; ring⟩

theorem exists_p_pow_mul_mem_of_dvd {z : 𝕎𝒪♭} {k : ℕ}
    (h : algebraMap 𝕎𝒪♭ 𝔸 (ξ ^ k) ∣ algebraMap 𝕎𝒪♭ 𝔸 z) :
    ∃ s : ℕ, (p : 𝕎𝒪♭) ^ s * z ∈ span {ξ ^ k} := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨⟨c', m⟩, hcm⟩ := IsLocalization.mk'_surjective (Submonoid.powers (p : 𝕎𝒪♭)) c
  obtain ⟨s, hs⟩ := Submonoid.mem_powers_iff _ _ |>.1 m.2
  have h2 : algebraMap 𝕎𝒪♭ 𝔸 (z * (m : 𝕎𝒪♭)) = algebraMap 𝕎𝒪♭ 𝔸 (ξ ^ k * c') := by
    rw [map_mul, hc, ← hcm, mul_assoc, IsLocalization.mk'_spec, map_mul]
  obtain ⟨r, hr⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (p : 𝕎𝒪♭)) h2
  obtain ⟨r', hr'⟩ := Submonoid.mem_powers_iff _ _ |>.1 r.2
  refine ⟨r' + s, mem_span_singleton.2 ⟨(p : 𝕎𝒪♭) ^ r' * c', ?_⟩⟩
  rw [← hs, ← hr'] at hr
  rw [pow_add]
  linear_combination hr

theorem mem_maximalIdeal_pow_of_forall_sub_mem {y : 𝔹} {k : ℕ}
    (h : ∀ M : ℕ, ∃ a : 𝕎𝒪♭, y - (p : 𝔹) ^ M * wittToBDeRhamPlus 𝒪 p a ∈ maximalIdeal 𝔹 ^ k) :
    y ∈ maximalIdeal 𝔹 ^ k := by
  set ξ₀ := kerThetaGenerator K p
  have hξ := ker_fontaineTheta_eq_span_kerThetaGenerator K p
  have hm : maximalIdeal 𝔹 ^ k = span {wittToBDeRhamPlus 𝒪 p (ξ₀ ^ k)} := by
    rw [maximalIdeal_bDeRhamPlus_eq_span hξ, span_singleton_pow, map_pow]
  obtain ⟨a₀, ha₀⟩ := h 0
  rw [pow_zero, one_mul] at ha₀
  suffices hs : a₀ ∈ span {ξ₀ ^ k} by
    have h1 : wittToBDeRhamPlus 𝒪 p a₀ ∈ maximalIdeal 𝔹 ^ k := by
      rw [hm]
      obtain ⟨d, rfl⟩ := mem_span_singleton.1 hs
      rw [map_mul]
      exact mul_mem_right _ _ (mem_span_singleton_self _)
    have := add_mem ha₀ h1
    rwa [sub_add_cancel] at this
  refine mem_span_xi_pow_of_forall_mem_sup hξ fun M => ?_
  obtain ⟨a, ha⟩ := h M
  have h2 : wittToBDeRhamPlus 𝒪 p (a₀ - (p : 𝕎𝒪♭) ^ M * a) ∈ maximalIdeal 𝔹 ^ k := by
    have := sub_mem ha ha₀
    rw [map_sub, map_mul, map_pow, map_natCast]
    convert this using 1
    ring
  rw [hm] at h2
  have h3 : toBDeRhamPlus 𝒪 p (algebraMap 𝕎𝒪♭ 𝔸 (a₀ - (p : 𝕎𝒪♭) ^ M * a)) ∈
      span {wittToBDeRhamPlus 𝒪 p ξ₀ ^ k} := by
    rw [← map_pow]; exact h2
  rw [toBDeRhamPlus_mem_span_pow_iff hξ, ← map_pow] at h3
  obtain ⟨s, hs⟩ := exists_p_pow_mul_mem_of_dvd h3
  have h4 := mem_span_xi_pow_of_p_pow_mul_mem hξ hs
  refine Submodule.mem_sup.2 ⟨(p : 𝕎𝒪♭) ^ M * a, mem_span_singleton.2 ⟨a, rfl⟩, _, h4, ?_⟩
  ring

end IsPerfectoidField

end GroundTheory.PAdicHodge
