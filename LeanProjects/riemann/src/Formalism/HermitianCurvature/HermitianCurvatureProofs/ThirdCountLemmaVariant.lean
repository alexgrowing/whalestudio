import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P

theorem hermitian_curvature_degree_count : C7.DegreeCount2 := by
  intro k r N M dl Dl hk hN hM h1 h2
  unfold C7.Nprime C7.nOf at *
  have hn : 2 ≤ k + 2 * r + 1 := by omega
  have b2 : 2 * M * Dl ≤ 2 * (3 * (N + 1)) * ((r + 1) * (2 * (k + 2 * r + 1) + 2)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 hM) h2
  have b3 : 2 * (3 * (N + 1)) * ((r + 1) * (2 * (k + 2 * r + 1) + 2)) ≤
      6 * (r + 1) * (3 * (N + 1)) * (k + 2 * r + 1) := by
    have e1 : 2 * (3 * (N + 1)) * ((r + 1) * (2 * (k + 2 * r + 1) + 2)) =
        (6 * (r + 1) * (N + 1)) * (2 * (k + 2 * r + 1) + 2) := by ring
    have e2 : 6 * (r + 1) * (3 * (N + 1)) * (k + 2 * r + 1) =
        (6 * (r + 1) * (N + 1)) * (3 * (k + 2 * r + 1)) := by ring
    rw [e1, e2]; exact Nat.mul_le_mul_left _ (by omega)
  have a2 : 1 ≤ (r + 1) * (k + 2 * r + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  refine ⟨Nat.mul_le_mul (Nat.mul_le_mul_left 2 hM) h1, b2.trans b3, by nlinarith, by nlinarith⟩

theorem third_count_lemma_variant : C7.LetterProductDoubleDegreeCount := by
  intro k r N d D hk h1 h2
  unfold C7.Dstar C7.Nprime C7.nOf at *
  have hn : 2 ≤ k + 2 * r + 1 := by omega
  have h3 : 3 * (r + 1) * d ≤ 3 * (r + 1) * ((N + 1) * (k + 2 * r + 1)) := Nat.mul_le_mul_left _ h1
  constructor
  · have e1 : (N + 1) * (r + 1) * (2 * (k + 2 * r + 1) + 2) + 3 * (r + 1) * ((N + 1) * (k + 2 * r + 1)) =
        ((r + 1) * (N + 1)) * (5 * (k + 2 * r + 1) + 2) := by ring
    have e2 : 6 * (r + 1) * (N + 1) * (k + 2 * r + 1) = ((r + 1) * (N + 1)) * (6 * (k + 2 * r + 1)) := by ring
    have h4 : ((r + 1) * (N + 1)) * (5 * (k + 2 * r + 1) + 2) ≤ ((r + 1) * (N + 1)) * (6 * (k + 2 * r + 1)) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  · have e2 : 6 * (r + 1) * (N + 1) * (k + 2 * r + 1) = ((r + 1) * (k + 2 * r + 1)) * (6 * (N + 1)) := by ring
    have e3 : 5 * (r + 1) * (3 * (N + 1) + 1) * (k + 2 * r + 1) =
        ((r + 1) * (k + 2 * r + 1)) * (5 * (3 * (N + 1) + 1)) := by ring
    rw [e2, e3]; exact Nat.mul_le_mul_left _ (by omega)

end Formalism.FourierDecayAlt.P
