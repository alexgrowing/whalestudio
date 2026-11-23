import Mathlib
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes

namespace GlobalTheory.Survey.CongruenceBoundParameters

theorem window_pos {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (W : ℝ) (hW : W ∈ baseSizes L) (n : ℤ)
    (hn : n ∈ window L W) : 0 < n := by
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have ht : (7 : ℝ) ≤ D.R.t := by
    have := D.R.three_m_lt_t; have := D.R.two_le_m; exact_mod_cast (by omega : 7 ≤ D.R.t)
  have hn1 : (1 : ℝ) ≤ D.R.n := by exact_mod_cast (show 1 ≤ D.R.n from D.R.ord_pos)
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hl := lStar_pos L
  have hη := L.etaSz_pos
  have hX : 1 ≤ L.sc.X' := Real.one_le_exp (by positivity)
  have hb' : 0 < L.sc.b' := by unfold Scale.b' Scale.a; positivity
  have hxn : 1 ≤ L.sc.x * D.R.n := by nlinarith
  have hw1 : L.sc.w'' D.R.n ≤ L.sc.b' := div_le_self hb'.le hxn
  have hw2 : L.sc.w'' D.R.n ≤ L.sc.b := by
    have : L.sc.w'' D.R.n = L.sc.b / (L.sc.X' * D.R.n) := by
      unfold Scale.w'' Scale.b' Scale.a; field_simp
    rw [this]; exact div_le_self hb.le (by nlinarith)
  have hWw : L.sc.w'' D.R.n ≤ W := by
    rcases hW with rfl | rfl | ⟨t, rfl⟩
    · exact hw2
    · exact le_rfl
    · have h1 := L.bT_ge t
      have h2 : (0 : ℝ) ≤ ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) := by
        exact_mod_cast Int.floor_nonneg.2 (by positivity)
      linarith
  have h1 := P.h0_ge.1
  have h2 : LevelStarExponents.h0 L ≤ L.etaSz := div_le_self hη.le (by linarith)
  have h3 := P.mteta
  have h4 : 16 * L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz :=
    mul_le_mul_of_nonneg_right (by nlinarith) hη.le
  have h5 : (sgPlus L : ℝ) ≤ 2 * L.sc.b / LevelStarExponents.lStar L := Int.floor_le _
  have h6 : 0 < L.sc.b / LevelStarExponents.lStar L := by positivity
  have h7 : 12 * L.sc.b / LevelStarExponents.lStar L = 12 * (L.sc.b / LevelStarExponents.lStar L) := by ring
  have h8 : 2 * L.sc.b / LevelStarExponents.lStar L = 2 * (L.sc.b / LevelStarExponents.lStar L) := by ring
  have : (0 : ℝ) < n := by linarith [hn.1]
  exact_mod_cast this

theorem two_lStar_lt_b {D : D7} (L : SizeData₂ D) : 2 * LevelStarExponents.lStar L < Real.exp L.sc.L := by
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have ht : 3 * (D.R.m : ℝ) < D.R.t := by exact_mod_cast D.R.three_m_lt_t
  have hn1 : (1 : ℝ) ≤ D.R.n := by exact_mod_cast (show 1 ≤ D.R.n from D.R.ord_pos)
  have hL : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hS := L.Sc_pos
  have hN : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ (D.R.k : ℝ) := Nat.cast_nonneg _
  have hA : (D.R.t : ℝ) ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2 := by
    have a1 : (1 : ℝ) ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 := one_le_mul_of_one_le_of_one_le hn1 (by nlinarith)
    have a2 : (1 : ℝ) ≤ L.sc.L ^ 2 := by nlinarith
    have a3 : (D.R.t : ℝ) ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) := by nlinarith
    nlinarith
  have hB : (0 : ℝ) ≤ (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L) := by positivity
  change 2 * LevelStarExponents.lStar L < L.sc.b
  unfold LevelStarExponents.lStar
  rw [← mul_div_assoc, div_lt_iff₀ (by linarith)]
  nlinarith

end GlobalTheory.Survey.CongruenceBoundParameters

end
