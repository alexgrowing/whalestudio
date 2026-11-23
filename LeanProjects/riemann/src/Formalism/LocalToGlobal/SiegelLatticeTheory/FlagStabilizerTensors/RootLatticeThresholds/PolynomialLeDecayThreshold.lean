import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierSizes
import Formalism.HermitianCurvature.StatementJCT

noncomputable section

namespace Formalism.L2.SG.Pf.CarrierT

theorem polynomial_le_decay_threshold (r k i : ℝ) (hr : 0 ≤ r) (hk : 0 ≤ k) (hi0 : 0 ≤ i) (hi : i ≤ r) :
    9 * (i + 1) * (127 * (r + 1) ^ 3 * (20 * (r + 1) * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 1) +
      20 * (r + 1) * (1 + 3 * (r + 1)) * i +
      (6 * i + 3 * (r + 1)) * (5 + 3 * (r + 1) * (20 * (r + 1) + 2) * (2 * r + k + 1) + 20 * (r + 1) * r) ≤
    25000 * (2 * r + k + 1) ^ 7 := by
  lift r to NNReal using hr
  lift k to NNReal using hk
  lift i to NNReal using hi0
  calc _ ≤ 9 * ((r : ℝ) + 1) * (127 * ((r : ℝ) + 1) ^ 3 * (20 * ((r : ℝ) + 1) * (2 * (r : ℝ) + k + 1) ^ 2 +
          (2 * (r : ℝ) + k + 1) ^ 3) + 1) +
        20 * ((r : ℝ) + 1) * (1 + 3 * ((r : ℝ) + 1)) * r +
        (6 * (r : ℝ) + 3 * ((r : ℝ) + 1)) * (5 + 3 * ((r : ℝ) + 1) * (20 * ((r : ℝ) + 1) + 2) *
          (2 * (r : ℝ) + k + 1) + 20 * ((r : ℝ) + 1) * r) := by gcongr
    _ ≤ 25000 * (2 * (r : ℝ) + k + 1) ^ 7 := by
      rw [← sub_nonneg]
      ring_nf
      positivity

def decayThreshold (Cc : ℝ) (k r : ℕ) : ℝ := (25000 + 21 * |Cc|) * (2 * (r : ℝ) + k + 1) ^ 7

section setting

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {Wp Wq : NumberField.InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

theorem sliceBudget_decayThreshold (S : Formalism.FourierDecayAlt.C.HidaSetting E Wp Wq) (Cc : ℝ) :
    Formalism.FourierDecayAlt.JCT.SliceBudget S (decayThreshold Cc S.G.k S.G.r) := by
  intro v i hi
  have hi' : (i : ℝ) ≤ S.G.r := by exact_mod_cast hi
  have hpoly := polynomial_le_decay_threshold (S.G.r : ℝ) (S.G.k : ℝ) (i : ℝ) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hi'
  have hN : (S.Ntop : ℝ) = 20 * ((S.G.r : ℝ) + 1) := by
    simp only [Formalism.FourierDecayAlt.C.HidaSetting.Ntop, Formalism.FourierDecayAlt.C.Kst]
    push_cast
    ring
  have hn7 : (0 : ℝ) ≤ (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 7 := by positivity
  calc _ = 9 * ((i : ℝ) + 1) * (127 * ((S.G.r : ℝ) + 1) ^ 3 * (20 * ((S.G.r : ℝ) + 1) *
          (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) + 1) +
        20 * ((S.G.r : ℝ) + 1) * (1 + 3 * ((S.G.r : ℝ) + 1)) * i +
        (6 * (i : ℝ) + 3 * ((S.G.r : ℝ) + 1)) * (5 + 3 * ((S.G.r : ℝ) + 1) * (20 * ((S.G.r : ℝ) + 1) + 2) *
          (2 * (S.G.r : ℝ) + S.G.k + 1) + 20 * ((S.G.r : ℝ) + 1) * S.G.r) := by
        simp only [Formalism.FourierDecayAlt.P5.Auser, Formalism.FourierDecayAlt.P5.mmUser, Formalism.FourierDecayAlt.P5.nV, hN]
        push_cast
        rw [hN]
    _ ≤ 25000 * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 7 := hpoly
    _ ≤ decayThreshold Cc S.G.k S.G.r := by
        unfold decayThreshold
        nlinarith [abs_nonneg Cc]

theorem poly_le_decayThreshold (S : Formalism.FourierDecayAlt.C.HidaSetting E Wp Wq) (Cc : ℝ) :
    Cc * ((S.G.r : ℝ) + 1) ^ 4 *
      ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) ≤ decayThreshold Cc S.G.k S.G.r := by
  have hN : (S.Ntop : ℝ) = 20 * ((S.G.r : ℝ) + 1) := by
    simp only [Formalism.FourierDecayAlt.C.HidaSetting.Ntop, Formalism.FourierDecayAlt.C.Kst]
    push_cast
    ring
  rw [hN]
  unfold decayThreshold
  have hs : (1 : ℝ) ≤ (S.G.r : ℝ) + 1 := by linarith [(Nat.cast_nonneg S.G.r : (0 : ℝ) ≤ S.G.r)]
  have hsn : (S.G.r : ℝ) + 1 ≤ 2 * (S.G.r : ℝ) + S.G.k + 1 := by
    linarith [(Nat.cast_nonneg S.G.r : (0 : ℝ) ≤ S.G.r), (Nat.cast_nonneg S.G.k : (0 : ℝ) ≤ S.G.k)]
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = (S.G.r : ℝ) + 1 := ⟨_, rfl⟩
  obtain ⟨n, hn_def⟩ : ∃ n : ℝ, n = 2 * (S.G.r : ℝ) + S.G.k + 1 := ⟨_, rfl⟩
  rw [← hs_def, ← hn_def]
  rw [← hs_def] at hs hsn
  rw [← hn_def] at hsn
  have hs0 : 0 ≤ s := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hX0 : 0 ≤ s ^ 4 * (20 * s * n ^ 2 + n ^ 3) :=
    mul_nonneg (pow_nonneg hs0 4) (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs0) (sq_nonneg n))
      (pow_nonneg hn0 3))
  have hX : s ^ 4 * (20 * s * n ^ 2 + n ^ 3) ≤ 21 * n ^ 7 := by
    have h4 : s ^ 4 ≤ n ^ 4 := pow_le_pow_left₀ hs0 hsn 4
    have h1 : 20 * s * n ^ 2 + n ^ 3 ≤ 21 * n ^ 3 := by nlinarith [sq_nonneg n]
    calc s ^ 4 * (20 * s * n ^ 2 + n ^ 3) ≤ n ^ 4 * (21 * n ^ 3) := by
          apply mul_le_mul h4 h1 (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs0) (sq_nonneg n))
            (pow_nonneg hn0 3)) (pow_nonneg hn0 4)
      _ = 21 * n ^ 7 := by ring
  have hn7 : 0 ≤ n ^ 7 := pow_nonneg hn0 7
  calc Cc * s ^ 4 * (20 * s * n ^ 2 + n ^ 3) = Cc * (s ^ 4 * (20 * s * n ^ 2 + n ^ 3)) := by ring
    _ ≤ |Cc| * (s ^ 4 * (20 * s * n ^ 2 + n ^ 3)) :=
        mul_le_mul_of_nonneg_right (le_abs_self Cc) hX0
    _ ≤ |Cc| * (21 * n ^ 7) := mul_le_mul_of_nonneg_left hX (abs_nonneg Cc)
    _ ≤ (25000 + 21 * |Cc|) * n ^ 7 := by nlinarith [abs_nonneg Cc]

end setting

end Formalism.L2.SG.Pf.CarrierT
