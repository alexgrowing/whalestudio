import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Grampd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.RealVec
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Gramdet
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Rypos

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

private theorem UpperTheory.V.KT.detlow_num (d : ℕ) (hd : d = 0 ∨ 2 ≤ d) (E P g : ℝ) (hE : 1 ≤ E)
    (hP : 0 ≤ P) (h1 : 1 ≤ (4 * (d : ℝ)) ^ d * g) (h2 : 2 ^ d * g = E * P ^ 2) :
    1 ≤ E * (d : ℝ) ^ d * P := by
  have hq : (1 : ℝ) ≤ ((d : ℝ) / 2) ^ d := by
    rcases hd with rfl | hd2
    · simp
    · apply one_le_pow₀
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd2
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      linarith
  have hprod : 1 ≤ E * P ^ 2 * (d : ℝ) ^ d * (d : ℝ) ^ d := by
    calc (1 : ℝ) ≤ ((d : ℝ) / 2) ^ d * ((4 * (d : ℝ)) ^ d * g) :=
          one_le_mul_of_one_le_of_one_le hq h1
      _ = E * P ^ 2 * (d : ℝ) ^ d * (d : ℝ) ^ d := by
        rw [← mul_assoc, ← mul_pow, show (d : ℝ) / 2 * (4 * d) = 2 * d * d by ring, mul_pow,
          mul_pow, ← h2]
        ring
  have hE0 : 0 ≤ E := by linarith
  have hX : 0 ≤ E * (d : ℝ) ^ d * P := mul_nonneg (mul_nonneg hE0 (by positivity)) hP
  have hsq : 1 ≤ (E * (d : ℝ) ^ d * P) ^ 2 := by
    calc (1 : ℝ) ≤ E * P ^ 2 * (d : ℝ) ^ d * (d : ℝ) ^ d := hprod
      _ ≤ E * (E * P ^ 2 * (d : ℝ) ^ d * (d : ℝ) ^ d) := by
        nlinarith [mul_nonneg (sub_nonneg.2 hE) (le_trans zero_le_one hprod)]
      _ = (E * (d : ℝ) ^ d * P) ^ 2 := by ring
  nlinarith

theorem UpperTheory.V.KT.detlow :
    ∀ (L : Type) [Field L] [NumberField L] [IsTotallyComplex L] (N : ℕ) (h : HS L N), h ∈ Ry L N →
    1 ≤ (I0 L N : ℝ) * ∏ w, (mat h w).det.re := by
  intro L _ _ _ N h hh
  classical
  obtain ⟨hherm, hquad, hreal, hbij⟩ := gramq L N h
  have hint0 : (intVec (0 : Fin N × BI L → ℤ) : KT.Lat L N) = 0 := by
    funext a
    simp [intVec]
  have hpos : ∀ c : Fin N × BI L → ℤ, c ≠ 0 →
      1 ≤ (fun i => (c i : ℝ)) ⬝ᵥ KT.gram h *ᵥ (fun i => (c i : ℝ)) := by
    intro c hc
    rw [hquad, hreal]
    have hne : intVec c ≠ 0 := fun h0 => hc (hbij.1 (h0.trans hint0.symm))
    exact hh (intVec c) hne
  obtain ⟨_, hdet⟩ := grampd (Fin N × BI L) (KT.gram h) hherm hpos
  have hcard : Fintype.card (Fin N × BI L) = dd L N := by
    rw [Fintype.card_prod, Fintype.card_fin, ← Module.finrank_eq_card_chooseBasisIndex,
      RingOfIntegers.rank, mul_comm]
  rw [hcard] at hdet
  have hgd := gramdet L N h
  have hPpos : 0 ≤ ∏ w, (mat h w).det.re := by
    apply Finset.prod_nonneg
    intro w _
    exact (Complex.pos_iff.1 ((rypos L N hh w).det_pos)).1.le
  have hE : (1 : ℝ) ≤ (absD L : ℝ) ^ N := by
    apply one_le_pow₀
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero L))
  have hd : dd L N = 0 ∨ 2 ≤ dd L N := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · left
      simp [dd, hN]
    · right
      have hr := Module.finrank_pos (R := ℚ) (M := L)
      have h2 : 2 ≤ Module.finrank ℚ L := by
        rw [IsTotallyComplex.finrank] at hr ⊢
        omega
      show 2 ≤ Module.finrank ℚ L * N
      nlinarith
  have key := UpperTheory.V.KT.detlow_num (dd L N) hd ((absD L : ℝ) ^ N) (∏ w, (mat h w).det.re)
    (KT.gram h).det hE hPpos hdet hgd
  have e : ((I0 L N : ℕ) : ℝ) = (absD L : ℝ) ^ N * (dd L N : ℝ) ^ (dd L N) := by
    unfold I0
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
  rw [e]
  exact key
