import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DvdPowZeroIff

open Matrix

namespace GlobalTheory.Hk3.IntWittBase

open Formalism.UG GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem eq_zero_of_forall_dvdPow {ϖ x : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (hx : ∀ k, DvdPow ϖ (k + 1) x) : x = 0 := by
  by_contra h0
  have hv0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  have key : ∀ N : ℕ, Valued.v x ≤ WithZero.exp (-(N : ℤ)) := by
    intro N
    obtain ⟨b, hb, hxb⟩ := hx N
    rw [hxb, map_mul, map_pow, hϖ]
    calc (WithZero.exp (-1 : ℤ)) ^ (N + 1) * Valued.v b ≤ (WithZero.exp (-1 : ℤ)) ^ (N + 1) * 1 :=
          mul_le_mul' le_rfl hb
      _ = WithZero.exp (-((N + 1 : ℕ) : ℤ)) := by
          rw [mul_one, ← WithZero.exp_nsmul]; congr 1; push_cast; ring
      _ ≤ WithZero.exp (-(N : ℤ)) := WithZero.exp_le_exp.2 (by push_cast; omega)
  obtain ⟨m, hm⟩ : ∃ m, Valued.v x = WithZero.exp m := ⟨_, (WithZero.exp_log hv0).symm⟩
  have h1 := key ((-m).toNat + 1)
  rw [hm, WithZero.exp_le_exp] at h1
  have := Int.self_le_toNat (-m)
  push_cast at h1
  omega

end GlobalTheory.Hk3.IntWittBase

namespace GlobalTheory.Hk3.IntWittBase

open Formalism.UG GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem dvdPow_map {ϖ : L} {σ : L →+* L} (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (hσϖ : σ ϖ = ϖ) {m : ℕ} {a : L}
    (h : DvdPow ϖ m a) : DvdPow ϖ m (σ a) := by
  obtain ⟨b, hb, rfl⟩ := h
  refine ⟨σ b, ?_, by rw [map_mul, map_pow, hσϖ]⟩
  show Valued.v (σ b) ≤ 1
  rw [hσv]; exact hb

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem cT_apply (σ : L →+* L) {n : ℕ} (A : Matrix (Fin n) (Fin n) L) (i j : Fin n) : cT σ A i j = σ (A j i) := rfl

theorem int_mul {n : ℕ} {A B : Matrix (Fin n) (Fin n) L} (hA : ∀ i j, A i j ∈ intL L) (hB : ∀ i j, B i j ∈ intL L) :
    ∀ i j, (A * B) i j ∈ intL L := by
  intro i j; rw [Matrix.mul_apply]; exact Subring.sum_mem _ fun l _ => mul_mem (hA i l) (hB l j)

theorem int_cT {σ : L →+* L} (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {n : ℕ} {A : Matrix (Fin n) (Fin n) L}
    (hA : ∀ i j, A i j ∈ intL L) : ∀ i j, cT σ A i j ∈ intL L := by
  intro i j; rw [cT_apply]; show Valued.v (σ _) ≤ 1; rw [hσv]; exact hA j i

theorem mc_mul_left {ϖ : L} {n m : ℕ} {A D : Matrix (Fin n) (Fin n) L} (hA : ∀ i j, A i j ∈ intL L)
    (hD : ∀ i j, DvdPow ϖ m (D i j)) : ∀ i j, DvdPow ϖ m ((A * D) i j) := by
  intro i j; rw [Matrix.mul_apply]; exact dvdPow_sum _ _ fun l _ => dvdPow_mul_int (hD l j) (hA i l)

theorem mc_mul_right {ϖ : L} {n m : ℕ} {D B : Matrix (Fin n) (Fin n) L} (hD : ∀ i j, DvdPow ϖ m (D i j))
    (hB : ∀ i j, B i j ∈ intL L) : ∀ i j, DvdPow ϖ m ((D * B) i j) := by
  intro i j; rw [Matrix.mul_apply]
  exact dvdPow_sum _ _ fun l _ => by rw [mul_comm]; exact dvdPow_mul_int (hD i l) (hB l j)

theorem mc_cT {ϖ : L} {σ : L →+* L} (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (hσϖ : σ ϖ = ϖ) {n m : ℕ}
    {D : Matrix (Fin n) (Fin n) L} (hD : ∀ i j, DvdPow ϖ m (D i j)) : ∀ i j, DvdPow ϖ m (cT σ D i j) := by
  intro i j; rw [cT_apply]; exact dvdPow_map hσv hσϖ (hD j i)

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem cT_sub (σ : L →+* L) {n : ℕ} (A B : Matrix (Fin n) (Fin n) L) : cT σ (A - B) = cT σ A - cT σ B := by
  ext i j; simp [cT_apply]

end GlobalTheory.Hk3.IntWittBase
