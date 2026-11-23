import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.SumIccMulEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BernoulliPolyReflection

open Finset UpperTheory.V.Bern

private theorem valuation_power_identity {R : Type} [CommRing R] {N p : ℕ} (χ : DirichletCharacter R N) (hp : p.Prime) (a : ℕ) :
    DirichletCharacter.changeLevel (dvd_mul_right N p) χ (a : ZMod (N * p))
      = χ (a : ZMod N) - if p ∣ a then χ (a : ZMod N) else 0 := by
  by_cases hc : a.Coprime (N * p)
  · have hpa : ¬ p ∣ a := fun h =>
      (Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.Coprime.coprime_mul_left_right hc).symm h
    rw [if_neg hpa, sub_zero]
    have := DirichletCharacter.changeLevel_eq_cast_of_dvd χ (dvd_mul_right N p) (ZMod.unitOfCoprime a hc)
    rw [ZMod.coe_unitOfCoprime, ZMod.cast_natCast (dvd_mul_right N p)] at this
    exact this
  · rw [MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])]
    split_ifs with h
    · simp
    · have : ¬ a.Coprime N := fun h' => hc (Nat.Coprime.mul_right h' ((Nat.Prime.coprime_iff_not_dvd hp).2 h).symm)
      rw [MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime]), sub_zero]

private theorem sum_divisible_eq_sum_mul {R : Type} [AddCommMonoid R] {N p : ℕ} (hp : 0 < p) (f : ℕ → R) :
    ∑ a ∈ Icc 1 (N * p), (if p ∣ a then f a else 0) = ∑ b ∈ Icc 1 N, f (p * b) := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun b _ => p * b) ?_ ?_ ?_ ?_
  · intro b hb
    simp only [mem_Icc, mem_filter] at hb ⊢
    refine ⟨⟨Nat.mul_pos hp hb.1, ?_⟩, dvd_mul_right _ _⟩
    rw [mul_comm]; exact Nat.mul_le_mul_right _ hb.2
  · intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_left hp h
  · intro a ha
    simp only [mem_Icc, mem_filter] at ha
    obtain ⟨⟨h1, h2⟩, b, rfl⟩ := ha
    refine ⟨b, ?_, rfl⟩
    simp only [mem_Icc]
    constructor
    · exact Nat.pos_of_mul_pos_left h1
    · rw [mul_comm] at h2; exact Nat.le_of_mul_le_mul_right h2 hp
  · intro _ _; rfl

theorem UpperTheory.V.Bern.b_step :
    ∀ {R : Type} [CommRing R] [Algebra ℚ R] {N p : ℕ} (k : ℕ) (χ : DirichletCharacter R N), 0 < N → p.Prime → 1 ≤ k → genB k (DirichletCharacter.changeLevel (dvd_mul_right N p) χ : ZMod (N * p) → R) = (1 - χ (p : ZMod N) * (p : R) ^ (k - 1)) * genB k χ := by
  intro R _ _ N p k χ hN hp hk
  have hc := b_comp (dvd_mul_right N p) k (χ : ZMod N → R) (Nat.mul_pos hN hp.pos)
  rw [sub_mul, one_mul]
  nth_rewrite 1 [← hc]
  unfold genB
  simp only [valuation_power_identity χ hp, map_natCast, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul]
  congr 1
  rw [sum_divisible_eq_sum_mul hp.pos (fun a => χ (a : ZMod N) * algebraMap ℚ R (bcoef (N * p) k a)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hs := (b_shift N k b hN).2.1 p hp.pos
  have e : ((k : ℤ) - 1) = ((k - 1 : ℕ) : ℤ) := by omega
  rw [e, zpow_natCast, mul_comm p N] at hs
  rw [hs, Nat.cast_mul, map_mul, map_mul, map_pow, map_natCast (algebraMap ℚ R)]
  ring
