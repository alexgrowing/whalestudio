import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.TateModule
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

open PadicInt

section Pairing

variable {A : Type*} [AddCommGroup A] {L : Type*} [Field L] (N : ℕ) (e : A → A → L)

theorem pairing_ne_zero (hpow : ∀ P Q, N • P = 0 → N • Q = 0 → e P Q ^ N = 1) (hN : N ≠ 0)
    {P Q : A} (hP : N • P = 0) (hQ : N • Q = 0) : e P Q ≠ 0 := by
  intro h
  have h1 := hpow P Q hP hQ
  rw [h, zero_pow hN] at h1
  exact zero_ne_one h1

theorem pairing_zero_left
    (hl : ∀ P Q R, N • P = 0 → N • Q = 0 → N • R = 0 → e (P + Q) R = e P R * e Q R)
    (hpow : ∀ P Q, N • P = 0 → N • Q = 0 → e P Q ^ N = 1) (hN : N ≠ 0)
    {R : A} (hR : N • R = 0) : e 0 R = 1 := by
  have h := hl 0 0 R (nsmul_zero N) (nsmul_zero N) hR
  rw [add_zero] at h
  have hne := pairing_ne_zero N e hpow hN (nsmul_zero N) hR
  exact mul_left_cancel₀ hne (h.symm.trans (mul_one _).symm)

theorem pairing_zero_right
    (hr : ∀ P Q R, N • P = 0 → N • Q = 0 → N • R = 0 → e P (Q + R) = e P Q * e P R)
    (hpow : ∀ P Q, N • P = 0 → N • Q = 0 → e P Q ^ N = 1) (hN : N ≠ 0)
    {P : A} (hP : N • P = 0) : e P 0 = 1 := by
  have h := hr P 0 0 hP (nsmul_zero N) (nsmul_zero N)
  rw [add_zero] at h
  have hne := pairing_ne_zero N e hpow hN hP (nsmul_zero N)
  exact mul_left_cancel₀ hne (h.symm.trans (mul_one _).symm)

theorem nsmul_nsmul_eq_zero {P : A} (hP : N • P = 0) (a : ℕ) : N • a • P = 0 := by
  rw [nsmul_swap, hP, nsmul_zero]

theorem pairing_nsmul_left
    (hl : ∀ P Q R, N • P = 0 → N • Q = 0 → N • R = 0 → e (P + Q) R = e P R * e Q R)
    (hpow : ∀ P Q, N • P = 0 → N • Q = 0 → e P Q ^ N = 1) (hN : N ≠ 0)
    {P R : A} (hP : N • P = 0) (hR : N • R = 0) (a : ℕ) : e (a • P) R = e P R ^ a := by
  induction a with
  | zero => rw [zero_nsmul, pow_zero, pairing_zero_left N e hl hpow hN hR]
  | succ a ih =>
    rw [succ_nsmul, hl _ _ _ (nsmul_nsmul_eq_zero N hP a) hP hR, ih, pow_succ]

theorem pairing_nsmul_right
    (hr : ∀ P Q R, N • P = 0 → N • Q = 0 → N • R = 0 → e P (Q + R) = e P Q * e P R)
    (hpow : ∀ P Q, N • P = 0 → N • Q = 0 → e P Q ^ N = 1) (hN : N ≠ 0)
    {P R : A} (hP : N • P = 0) (hR : N • R = 0) (a : ℕ) : e P (a • R) = e P R ^ a := by
  induction a with
  | zero => rw [zero_nsmul, pow_zero, pairing_zero_right N e hr hpow hN hP]
  | succ a ih =>
    rw [succ_nsmul, hr _ _ _ hP (nsmul_nsmul_eq_zero N hR a) hR, ih, pow_succ]

theorem pairing_comb
    (hl : ∀ P Q R, N • P = 0 → N • Q = 0 → N • R = 0 → e (P + Q) R = e P R * e Q R)
    (hr : ∀ P Q R, N • P = 0 → N • Q = 0 → N • R = 0 → e P (Q + R) = e P Q * e P R)
    (hpow : ∀ P Q, N • P = 0 → N • Q = 0 → e P Q ^ N = 1)
    (hself : ∀ P, N • P = 0 → e P P = 1) (hN : N ≠ 0)
    {P Q : A} (hP : N • P = 0) (hQ : N • Q = 0) (a c b d : ℕ) :
    e (a • P + c • Q) (b • P + d • Q) * e P Q ^ (c * b) = e P Q ^ (a * d) := by
  have haP := nsmul_nsmul_eq_zero N hP a
  have hcQ := nsmul_nsmul_eq_zero N hQ c
  have hbP := nsmul_nsmul_eq_zero N hP b
  have hdQ := nsmul_nsmul_eq_zero N hQ d
  have hsum : N • (b • P + d • Q) = 0 := by rw [nsmul_add, hbP, hdQ, add_zero]
  have hPQ : N • (P + Q) = 0 := by rw [nsmul_add, hP, hQ, add_zero]
  have halt : e Q P * e P Q = 1 := by
    have h := hself (P + Q) hPQ
    rw [hl P Q _ hP hQ hPQ, hr P P Q hP hP hQ, hr Q P Q hQ hP hQ, hself P hP, hself Q hQ] at h
    rw [← h]
    ring
  rw [hl _ _ _ haP hcQ hsum, hr _ _ _ haP hbP hdQ, hr _ _ _ hcQ hbP hdQ,
    pairing_nsmul_left N e hl hpow hN hP hbP, pairing_nsmul_left N e hl hpow hN hP hdQ,
    pairing_nsmul_left N e hl hpow hN hQ hbP, pairing_nsmul_left N e hl hpow hN hQ hdQ,
    pairing_nsmul_right N e hr hpow hN hP hP, pairing_nsmul_right N e hr hpow hN hP hQ,
    pairing_nsmul_right N e hr hpow hN hQ hP, pairing_nsmul_right N e hr hpow hN hQ hQ,
    hself P hP, hself Q hQ]
  calc _ = e P Q ^ (a * d) * (e Q P * e P Q) ^ (c * b) := by ring
    _ = _ := by rw [halt, one_pow, mul_one]

end Pairing

section Determinant

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {A : Type*} [AddCommGroup A]

omit hℓ in

theorem TateModule.exists_eq_nsmul_of_apply_one_eq_zero (t : TateModule ℓ A)
    (h : (t : ℕ → A) 1 = 0) : ∃ s : TateModule ℓ A, t = ℓ • s := by
  refine ⟨⟨fun j => (t : ℕ → A) (j + 1), fun j => ?_, fun j => TateModule.nsmul_succ t (j + 1)⟩, ?_⟩
  · show ℓ ^ j • (t : ℕ → A) (j + 1) = 0
    rw [add_comm, TateModule.pow_nsmul_add t 1 j, h]
  · refine Subtype.ext (funext fun j => ?_)
    rw [AddSubgroup.coe_nsmul, Pi.smul_apply]
    exact (TateModule.nsmul_succ t j).symm

theorem TateModule.basis_apply_one_ne_zero {ι : Type*} (b : Module.Basis ι ℤ_[ℓ] (TateModule ℓ A))
    (i : ι) : ((b i : TateModule ℓ A) : ℕ → A) 1 ≠ 0 := by
  classical
  intro h0
  obtain ⟨s, hs⟩ := TateModule.exists_eq_nsmul_of_apply_one_eq_zero (b i) h0
  have h := congrArg (fun u => b.repr u i) hs
  simp only [Module.Basis.repr_self, Finsupp.single_eq_same, map_nsmul, Finsupp.smul_apply,
    nsmul_eq_mul] at h
  exact (mem_nonunits_iff.mp PadicInt.p_nonunit) (isUnit_iff_exists_inv.mpr ⟨_, h.symm⟩)

end Determinant

end GroundTheory.Arith.Abelian
