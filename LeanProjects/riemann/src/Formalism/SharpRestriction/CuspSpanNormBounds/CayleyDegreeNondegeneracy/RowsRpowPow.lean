import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsNum

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.HermitianLatticeCounting

theorem rows_rpow_pow {b : ℝ} (hb : 0 < b) (x : ℝ) (n : ℕ) : (b ^ x) ^ n = b ^ (x * n) := by
  first
    | exact (Real.rpow_mul_natCast hb.le x n).symm
    | (rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le])

theorem rows_num_Q {f r : ℕ} {b pe E1 cr δ : ℝ} (hb : 2 ≤ b) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1) :
    (1 + δ) * (((b ^ pe) ^ E1) ^ 2 * ((b ^ pe) ^ cr) ^ 2) * ((41 ^ f * (b ^ pe) ^ 3) ^ ((r + 1) ^ 2)) ^ 2 ≤
      b ^ (1 + 12 * (f : ℝ) * ((r : ℝ) + 1) ^ 2 + pe * (2 * E1 + 2 * cr + 6 * ((r : ℝ) + 1) ^ 2)) := by
  have hb0 : 0 < b := by linarith
  have hrp : ∀ y z : ℝ, (b ^ y) ^ z = b ^ (y * z) := fun y z => (Real.rpow_mul hb0.le y z).symm
  have h6 : (41 : ℝ) ≤ b ^ 6 := by
    have h2 : (2 : ℝ) ^ 6 ≤ b ^ 6 := by gcongr
    norm_num at h2
    linarith
  have h41 : (41 : ℝ) ^ f ≤ b ^ (6 * (f : ℝ)) := by
    calc (41 : ℝ) ^ f ≤ (b ^ 6) ^ f := by gcongr
      _ = b ^ (6 * (f : ℝ)) := by
        rw [← pow_mul, ← Real.rpow_natCast]
        congr 1 <;> push_cast <;> ring
  have e0 : (b ^ pe) ^ 3 = b ^ (3 * pe) := by
    rw [rows_rpow_pow hb0]
    congr 1 <;> push_cast <;> ring
  have hA : (41 : ℝ) ^ f * (b ^ pe) ^ 3 ≤ b ^ (6 * (f : ℝ) + 3 * pe) := by
    rw [Real.rpow_add hb0, e0]
    gcongr
    all_goals first | exact h41 | positivity
  have e1 : ((b ^ pe) ^ E1) ^ 2 = b ^ (2 * pe * E1) := by
    rw [hrp, rows_rpow_pow hb0]
    congr 1 <;> push_cast <;> ring
  have e2 : ((b ^ pe) ^ cr) ^ 2 = b ^ (2 * pe * cr) := by
    rw [hrp, rows_rpow_pow hb0]
    congr 1 <;> push_cast <;> ring
  have e3 : ((b ^ (6 * (f : ℝ) + 3 * pe)) ^ ((r + 1) ^ 2)) ^ 2 =
      b ^ (12 * (f : ℝ) * ((r : ℝ) + 1) ^ 2 + 6 * pe * ((r : ℝ) + 1) ^ 2) := by
    rw [rows_rpow_pow hb0, rows_rpow_pow hb0]
    congr 1 <;> push_cast <;> ring
  have h1δ : 1 + δ ≤ b ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    linarith
  calc (1 + δ) * (((b ^ pe) ^ E1) ^ 2 * ((b ^ pe) ^ cr) ^ 2) * ((41 ^ f * (b ^ pe) ^ 3) ^ ((r + 1) ^ 2)) ^ 2
      ≤ b ^ (1 : ℝ) * (((b ^ pe) ^ E1) ^ 2 * ((b ^ pe) ^ cr) ^ 2) *
          ((b ^ (6 * (f : ℝ) + 3 * pe)) ^ ((r + 1) ^ 2)) ^ 2 := by
        gcongr
        all_goals first | exact h1δ | exact hA | positivity
    _ = b ^ (1 : ℝ) * (b ^ (2 * pe * E1) * b ^ (2 * pe * cr)) *
          b ^ (12 * (f : ℝ) * ((r : ℝ) + 1) ^ 2 + 6 * pe * ((r : ℝ) + 1) ^ 2) := by
        rw [e1, e2, e3]
    _ = _ := by
        rw [← Real.rpow_add hb0, ← Real.rpow_add hb0, ← Real.rpow_add hb0]
        congr 1
        ring

theorem rows_num_nd {k m f s r : ℕ} {b g v Γ c C pe E1 cr δ rD XiP : ℝ} {Xi : ℕ → ℝ}
    (hb : 2 ≤ b) (hg : 0 < g) (hv : 0 < v) (hΓ : 0 ≤ Γ) (hc : 0 ≤ c) (hcC : c ≤ C) (hC : 1 ≤ C)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1) (hrD : 0 ≤ rD) (hXiP : 0 ≤ XiP) (hXi : XiP ≤ Xi s)
    (hexp : 1 + 12 * (f : ℝ) * ((r : ℝ) + 1) ^ 2 + pe * (2 * E1 + 2 * cr + 6 * ((r : ℝ) + 1) ^ 2) ≤
      C * (m : ℝ) ^ 2 * f * (C * ((s : ℝ) + m) * (m : ℝ) ^ 2)) :
    (2 / g) ^ ((s - 1) * k * f) * ((k : ℝ) * v / (Real.exp 1 * Real.pi)) ^ (k * f) *
        (XiP * (((b ^ pe) ^ E1) ^ 2 * ((b ^ pe) ^ cr) ^ 2 * (c * s * f) ^ (6 * s * f) * Γ)) * ((1 + δ) * rD) *
        ((41 ^ f * (b ^ pe) ^ 3) ^ ((r + 1) ^ 2)) ^ 2 ≤
      LatticeSumBounds.ndRow C k m f s b g v Γ Xi * rD := by
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hC0 : 0 < C := by linarith
  have hXis : 0 ≤ Xi s := hXiP.trans hXi
  have hH : b ^ (1 + 12 * (f : ℝ) * ((r : ℝ) + 1) ^ 2 + pe * (2 * E1 + 2 * cr + 6 * ((r : ℝ) + 1) ^ 2)) ≤
      Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) := by
    unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH
    rw [← Real.rpow_mul hb0.le]
    first
      | exact Real.rpow_le_rpow_of_exponent_le hb1 hexp
      | exact (Real.rpow_le_rpow_left_iff (by linarith)).2 hexp
  have hB := (rows_num_Q (f := f) (r := r) (pe := pe) (E1 := E1) (cr := cr) hb hδ0 hδ).trans hH
  have hep : 1 ≤ Real.exp 1 * Real.pi := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h2 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    nlinarith
  have hkv : 0 ≤ (k : ℝ) * v := by positivity
  have hq : (k : ℝ) * v / (Real.exp 1 * Real.pi) ≤ (k : ℝ) * v * C := by
    have hd : (k : ℝ) * v / (Real.exp 1 * Real.pi) ≤ (k : ℝ) * v := by
      first
        | exact div_le_self hkv hep
        | (rw [div_le_iff₀ (by positivity)]; nlinarith)
    nlinarith
  have hK : ((k : ℝ) * v / (Real.exp 1 * Real.pi)) ^ (k * f) ≤ ((k : ℝ) * v) ^ (k * f) * C ^ (k * f) := by
    rw [← mul_pow]
    gcongr
  calc _ = ((2 / g) ^ ((s - 1) * k * f) * ((k : ℝ) * v / (Real.exp 1 * Real.pi)) ^ (k * f) * XiP *
          (c * s * f) ^ (6 * s * f) * Γ * rD) *
        ((1 + δ) * (((b ^ pe) ^ E1) ^ 2 * ((b ^ pe) ^ cr) ^ 2) * ((41 ^ f * (b ^ pe) ^ 3) ^ ((r + 1) ^ 2)) ^ 2) := by
        ring
    _ ≤ ((2 / g) ^ ((s - 1) * k * f) * (((k : ℝ) * v) ^ (k * f) * C ^ (k * f)) * Xi s *
          (C * s * f) ^ (6 * s * f) * Γ * rD) *
        Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) := by
        gcongr
        all_goals first | assumption | positivity
    _ = Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C k m f s b g v Γ Xi * rD := by
        unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow
        ring

end Formalism.MainNotions.BridgeLemma₂
