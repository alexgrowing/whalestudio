import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScaleStatement
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem cloudUnit_poly_bounds (x c F K cD k m N f L : ℝ) (hx : 1 ≤ x) (hc : 1 ≤ c) (hcx : c ≤ x) (hF : 1 ≤ F)
    (hK : 1 ≤ K) (hcD : 5 * c + F * c + 406 * K + 412 ≤ cD)
    (hk0 : 0 ≤ k) (hk : k ≤ x ^ (5 : ℝ)) (hm0 : 0 ≤ m) (hm : m ≤ x) (hN0 : 0 ≤ N) (hN : N ≤ x ^ (402 : ℝ))
    (hf0 : 0 ≤ f) (hf : f ≤ x ^ (3 : ℝ)) (hL0 : 0 ≤ L) (hL : L ≤ x) :
    (k ^ c * (c * m) ^ 3 / (6 * x ^ (-F)) ^ c ≤ x ^ cD ∧ c * m * N ≤ x ^ cD ∧
      k ^ c * (c * m ^ 4 * L) ^ 4 ≤ x ^ cD ∧ N * m ^ 10 ≤ x ^ cD) ∧ (N * f * L) ^ K ≤ x ^ cD := by
  have hx0 : 0 < x := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hFc : 0 ≤ F * c := by positivity
  have mono : ∀ a : ℝ, a ≤ 5 * c + F * c + 406 * K + 412 → x ^ a ≤ x ^ cD := fun a ha =>
    Real.rpow_le_rpow_of_exponent_le hx (ha.trans hcD)
  have hkc : k ^ c ≤ x ^ (5 * c) := by
    rw [Real.rpow_mul hx0.le]
    exact Real.rpow_le_rpow hk0 hk hc0
  have hnat : ∀ n : ℕ, x ^ n = x ^ (n : ℝ) := fun n => (Real.rpow_natCast x n).symm
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · have h1 : (c * m) ^ 3 ≤ x ^ (6 : ℝ) := by
      calc (c * m) ^ 3 ≤ (x * x) ^ 3 := by gcongr
        _ = x ^ (6 : ℕ) := by ring
        _ = x ^ (6 : ℝ) := by rw [hnat]; norm_num
    have hp : 0 < x ^ (-F) := Real.rpow_pos_of_pos hx0 _
    have h2 : x ^ (-(F * c)) ≤ (6 * x ^ (-F)) ^ c := by
      rw [← neg_mul, Real.rpow_mul hx0.le]
      exact Real.rpow_le_rpow hp.le (by linarith) hc0
    have hq : 0 < x ^ (-(F * c)) := Real.rpow_pos_of_pos hx0 _
    calc k ^ c * (c * m) ^ 3 / (6 * x ^ (-F)) ^ c ≤ x ^ (5 * c) * x ^ (6 : ℝ) / x ^ (-(F * c)) := by gcongr
      _ = x ^ (5 * c + 6 + F * c) := by
          rw [← Real.rpow_add hx0, ← Real.rpow_sub hx0]; congr 1; ring
      _ ≤ x ^ cD := mono _ (by linarith)
  · calc c * m * N ≤ x * x * x ^ (402 : ℝ) := by gcongr
      _ = x ^ (2 : ℕ) * x ^ (402 : ℝ) := by ring
      _ = x ^ (404 : ℝ) := by rw [hnat, ← Real.rpow_add hx0]; norm_num
      _ ≤ x ^ cD := mono _ (by linarith)
  · calc k ^ c * (c * m ^ 4 * L) ^ 4 ≤ x ^ (5 * c) * (x * x ^ 4 * x) ^ 4 := by gcongr
      _ = x ^ (5 * c) * x ^ (24 : ℕ) := by ring
      _ = x ^ (5 * c + 24) := by rw [hnat, ← Real.rpow_add hx0]; norm_num
      _ ≤ x ^ cD := mono _ (by linarith)
  · calc N * m ^ 10 ≤ x ^ (402 : ℝ) * x ^ 10 := by gcongr
      _ = x ^ (412 : ℝ) := by rw [hnat, ← Real.rpow_add hx0]; norm_num
      _ ≤ x ^ cD := mono _ (by linarith)
  · have h1 : N * f * L ≤ x ^ (406 : ℝ) := by
      calc N * f * L ≤ x ^ (402 : ℝ) * x ^ (3 : ℝ) * x := by gcongr
        _ = x ^ (406 : ℝ) := by
          rw [← Real.rpow_add hx0, ← Real.rpow_add_one hx0.ne']; norm_num
    calc (N * f * L) ^ K ≤ (x ^ (406 : ℝ)) ^ K := Real.rpow_le_rpow (by positivity) h1 (by linarith)
      _ = x ^ (406 * K) := by rw [← Real.rpow_mul hx0.le]
      _ ≤ x ^ cD := mono _ (by linarith)

theorem szRow_cloudUnit_lower : SzRow (fun C D L => ((D.R.k : ℝ) ^ C.P.CDel * (C.P.CDel * D.R.m) ^ 3 / D.div.etaF ^ C.P.CDel ≤ (D.s.Del : ℝ) ∧ C.P.CDel * D.R.m * D.R.N D.R.m ≤ (D.s.Del : ℝ) ∧ (D.R.k : ℝ) ^ C.P.CDel * (C.P.CDel * (D.R.m : ℝ) ^ 4 * L.sc.L) ^ 4 ≤ (D.s.Del : ℝ) ∧ (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 ≤ (D.s.Del : ℝ)) ∧ (((D.R.N D.R.m : ℝ) * D.R.f * L.sc.L) ^ C.P.CCount ≤ (D.s.Del : ℝ))) := by
  intro eps h0 h1 C hC
  obtain ⟨x0, hx0⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps h0 h1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hmid, hlast⟩ := hC
  have hF : 1 ≤ C.P.CF := hmid _ (by simp [FC.cMid])
  have hc : 1 ≤ C.P.CDel := hlast _ (by simp [FC.cLast])
  have hK : 1 ≤ C.P.CCount := hlast _ (by simp [FC.cLast])
  refine ⟨5 * C.P.CDel + C.P.CF * C.P.CDel + 406 * C.P.CCount + 412, fun cD hcD => ⟨0, fun ch _ =>
    ⟨max x0 C.P.CDel, fun D L he hx V => ?_⟩⟩⟩
  have hxc : C.P.CDel ≤ L.sc.x := (le_max_right _ _).trans hx
  obtain ⟨hf, hm, hr, hkr, -, hL, hL1, -, -, -, -, -, -, -, hN, -, -⟩ :=
    hx0 L.sc D.R he ((le_max_left _ _).trans hx) V.ranks
  have hk : (D.R.k : ℝ) ≤ L.sc.x ^ (5 : ℝ) := le_trans (by exact_mod_cast hkr) hr
  have hDel : L.sc.x ^ cD ≤ (D.s.Del : ℝ) := by
    rw [V.Del_eq, Rat.cast_natCast]
    exact Nat.le_ceil _
  obtain ⟨⟨a1, a2, a3, a4⟩, a5⟩ := cloudUnit_poly_bounds L.sc.x C.P.CDel C.P.CF C.P.CCount cD D.R.k D.R.m
    (D.R.N D.R.m) D.R.f L.sc.L (hc.trans hxc) hc hxc hF hK hcD (Nat.cast_nonneg _) hk (Nat.cast_nonneg _) hm
    (Nat.cast_nonneg _) hN (Nat.cast_nonneg _) hf (by linarith) hL
  rw [← V.etaF_eq] at a1
  exact ⟨⟨a1.trans hDel, a2.trans hDel, a3.trans hDel, a4.trans hDel⟩, a5.trans hDel⟩

end GlobalTheory.EX
