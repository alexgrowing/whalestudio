import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdditiveCharacterPsi

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P

theorem weight_determinant : C7.DetW := by
  intro s
  induction s with
  | zero => simp [G.wMat]
  | succ n ih =>
    rw [(det_weyl_matrix n).1, ih, ← pow_add]
    congr 1
    rcases n with _ | m
    · simp
    · have e : (m + 1 + 1) * (m + 1 + 1 - 1) = (m + 1) * (m + 1 - 1) + 2 * (m + 1) := by
        simp only [Nat.add_sub_cancel]; ring
      rw [e, Nat.add_mul_div_left _ _ (by norm_num)]
      ring

theorem equal_roots_determinant : C7.DEqualRoots := by
  intro s D'' c t z hs hz
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hz
  have e : (G.wMat (m + 1 - 1)).det = (G.wMat m).det := rfl
  rw [e, (det_weyl_matrix m).1, hz, Nat.add_sub_cancel]
  have h1 : ((-1 : ℂ)) ^ m * (-1) ^ (m + 1 + 1) = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨m + 1, by ring⟩
  linear_combination (-(D'' * (G.wMat m).det * c * t ^ m)) * h1

theorem equal_roots_of_parts : C7.DEqualOfParts := fun _ => equal_roots_determinant

theorem nprime_le_bound : C7.NprimeLe := by
  intro N h; unfold C7.Nprime; omega

theorem threshold_exponent_estimate : C7.ThresholdE := by
  intro k r N AP hk hN hAP
  have h : 126 * (r + 1) ^ 3 * (C7.Nprime N * C7.nOf k r ^ 2 + C7.nOf k r ^ 3) +
      C7.B0 r * C7.mmP r (C7.Nprime N) (C7.nOf k r) + 12 * (r + 1) * C7.Nprime N * C7.nOf k r ≤
      915 * (r + 1) ^ 3 * (N * C7.nOf k r ^ 2 + C7.nOf k r ^ 3) := by
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hN
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hk
    unfold C7.Nprime C7.nOf C7.B0 C7.mmP
    refine le_trans (Nat.le_add_right _ (537*a*b^2*r^3 + 1611*a*b^2*r^2 + 1611*a*b^2*r + 537*a*b^2 + 2148*a*b*r^4 + 8592*a*b*r^3 + 12861*a*b*r^2 + 8502*a*b*r + 2085*a*b + 2148*a*r^5 + 10740*a*r^4 + 21426*a*r^3 + 21246*a*r^2 + 10434*a*r + 2022*a + 789*b^3*r^3 + 2367*b^3*r^2 + 2367*b^3*r + 789*b^3 + 5271*b^2*r^4 + 20706*b^2*r^3 + 30492*b^2*r^2 + 19950*b^2*r + 4893*b^2 + 11616*b*r^5 + 56568*b*r^4 + 110085*b*r^3 + 106926*b*r^2 + 51753*b*r + 9960*b + 8460*r^6 + 49248*r^5 + 119286*r^4 + 153702*r^3 + 110898*r^2 + 42339*r + 6645)) (le_of_eq ?_)
    ring
  have hR := (Nat.cast_le (α := ℝ)).2 h
  push_cast at hR
  linarith

theorem budget_sum_estimate : C7.BudgetSum := by
  intro r N' n d D h1 h2; unfold C7.B0; nlinarith

theorem c7_letter_product_degree_count : C7.LetterProductDegreeCount := by
  intro k r N d D hk h1 h2; unfold C7.Dstar C7.Nprime C7.nOf at *
  constructor <;> nlinarith

theorem degree_count_identity : C7.DegreeCount := by
  intro k r N M dl Dl hk hN hM h1 h2; unfold C7.Nprime C7.nOf at *
  have a2 : 1 ≤ (r + 1) * (k + 2 * r + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have a3 := Nat.mul_le_mul_left (6 * (3 * (N + 1))) a2
  have b1 : Dl ≤ (r + 1) * (k + 2 * r + 1) + 2 * (r + 1) := by nlinarith
  have b2 : 2 * M * Dl ≤ 2 * (3 * (N + 1)) * ((r + 1) * (k + 2 * r + 1) + 2 * (r + 1)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 hM) b1
  have b3 : 2 * (3 * (N + 1)) * ((r + 1) * (k + 2 * r + 1) + 2 * (r + 1)) ≤
      6 * (r + 1) * (3 * (N + 1)) * (k + 2 * r + 1) := by
    have hP : (r + 1) * (N + 1) * 1 ≤ (r + 1) * (N + 1) * (k + 2 * r + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    nlinarith [hP]
  refine ⟨Nat.mul_le_mul (Nat.mul_le_mul_left 2 hM) h1, b2.trans b3, by nlinarith, by nlinarith, by nlinarith⟩

theorem eigenvalue_shift : C7.EigenShift := by
  intro k r Y a i; unfold Formalism.FourierDecayAlt.Q.uC C7.lamOf C7.nOf Formalism.FourierDecayAlt.Q.mdim; simp; ring

end Formalism.FourierDecayAlt.P
