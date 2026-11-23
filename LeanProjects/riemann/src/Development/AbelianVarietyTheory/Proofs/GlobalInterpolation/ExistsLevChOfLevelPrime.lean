import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparison
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScale
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormOnePrimeElements
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModEqOneOfNorm

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

namespace GlobalTheory.EX.OB

theorem exists_levCh_of_levelPrime : LevelPrime → ∀ (eps cs : ℝ) (C : FC), 0 < eps → eps < 1 / 52 → 0 < cs → Std C → ∃ x0 : ℝ, ∀ (cD ch : ℝ) (s : Scale) (P : PreCh) (q1 : ℕ) (a b : P.R.A → ℤ) (c : P.Word → Fin (P.R.k - 2) → Bool) (du : P.Word → ℕ) (Ds : ℝ), s.eps = eps → x0 ≤ s.x → ChOK s C cD ch P q1 a b c → (∀ u, 0 < du u) → 0 < Ds → (∀ u, cs * P.R.m * s.L ≤ Real.log ((Ds / du u) ^ ((1 : ℝ) / (P.R.f * P.R.k)) * GamS C s P.R ^ (-(2 : ℝ) / (P.R.f * P.R.k)))) → ∃ Lv : LevCh P, Lv.duStar = du ∧ Lv.Dstar = Ds ∧ Lv.GamP = GamS C s P.R := by
  intro hLP eps cs C he he' hcs hC
  obtain ⟨x1, h1⟩ := hLP eps cs he he' hcs
  obtain ⟨x2, h2⟩ := GlobalTheory.scale_poly_comparison eps 41 1 he one_pos
  obtain ⟨x3, h3⟩ := GlobalTheory.EX.rank_basic_bounds eps he he'
  refine ⟨max (max x1 x2) (max x3 (max 2 ((1 / cs) ^ 4))), ?_⟩
  intro cD ch s P q1 a b c du Ds hs hx hOK hdu hDs hwin
  simp only [max_le_iff] at hx
  obtain ⟨⟨hx1, hx2⟩, hx3, hx4, hx5⟩ := hx
  obtain ⟨-, -, hb, -⟩ := h2 s hs hx2
  obtain ⟨-, -, hr, hkr, -, -, hL1, -, -, -, -, -, -, -, -, hm, -⟩ := h3 s P.R hs hx3 hOK.rank
  have hx0 : 0 < s.x := by linarith
  have hxone : 1 ≤ s.x := by linarith
  have hX1 : 1 ≤ s.X' := Real.one_le_exp (by positivity)
  have hb0 : 0 < s.b := Real.exp_pos _
  have hG : 1 ≤ C.CGam := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])
  have hm2 : (2 : ℝ) ≤ P.R.m := by exact_mod_cast P.R.two_le_m
  have hmf : (P.R.m : ℝ) ≤ P.R.f := by exact_mod_cast P.R.m_le_f
  have hGam : 1 < GamS C s P.R := by
    unfold GamS
    rw [Real.one_lt_exp_iff]
    have : (0 : ℝ) < P.R.f := by linarith
    have : (0 : ℝ) < P.R.m := by linarith
    have : 0 < C.CGam := by linarith
    have : 0 < s.L := by linarith
    positivity

  have hk : (P.R.k : ℝ) ≤ s.x ^ 5 := by
    have : (P.R.k : ℝ) ≤ P.R.r := by exact_mod_cast hkr
    have e : s.x ^ (5 : ℝ) = s.x ^ 5 := by exact_mod_cast Real.rpow_natCast s.x 5
    exact this.trans (hr.trans_eq e)
  have hb41 : s.x ^ 41 ≤ s.b := by
    have e : s.x ^ (41 : ℝ) = s.x ^ 41 := by exact_mod_cast Real.rpow_natCast s.x 41
    rw [e, Real.rpow_one] at hb
    exact (le_mul_of_one_le_right (by positivity) hX1).trans hb
  have hk8 : 2 * (P.R.k : ℝ) ^ 8 ≤ s.b := by
    have h8 : (P.R.k : ℝ) ^ 8 ≤ (s.x ^ 5) ^ 8 := pow_le_pow_left₀ (by positivity) hk 8
    calc 2 * (P.R.k : ℝ) ^ 8 ≤ s.x * (s.x ^ 5) ^ 8 := mul_le_mul hx4 h8 (by positivity) hx0.le
      _ = s.x ^ 41 := by ring
      _ ≤ s.b := hb41
  have hg : ∀ i, (P.H.g i : ℝ) ≤ s.b ^ 9 := fun i => by
    calc (P.H.g i : ℝ) ≤ 2 * ((P.R.k : ℝ) * s.b) ^ 8 := (hOK.val.2.2.2.2.1 i).2
      _ = (2 * (P.R.k : ℝ) ^ 8) * s.b ^ 8 := by ring
      _ ≤ s.b * s.b ^ 8 := mul_le_mul_of_nonneg_right hk8 (by positivity)
      _ = s.b ^ 9 := by ring

  have hcm : 1 ≤ cs * P.R.m := by
    have a1 : 1 / cs ≤ s.x ^ ((1 : ℝ) / 4) := by
      have a0 : ((1 / cs) ^ 4) ^ ((1 : ℝ) / 4) ≤ s.x ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow (by positivity) hx5 (by norm_num)
      have e : ((1 / cs) ^ 4) ^ ((1 : ℝ) / 4) = 1 / cs := by
        have := Real.pow_rpow_inv_natCast (x := 1 / cs) (n := 4) (by positivity) (by norm_num)
        simpa using this
      rwa [e] at a0
    have a2 : s.x ^ ((1 : ℝ) / 4) ≤ s.x ^ ((1 : ℝ) / 2 - s.eps / 16) :=
      Real.rpow_le_rpow_of_exponent_le hxone (by rw [hs]; linarith)
    have a3 : 1 / cs ≤ P.R.m := a1.trans (a2.trans hm)
    rw [div_le_iff₀ hcs] at a3
    linarith
  have hXL : s.X' ≤ Real.exp (cs * P.R.m * s.L) := by
    unfold Scale.X'
    refine Real.exp_le_exp.2 ?_
    have a1 : s.x ^ (s.eps / 3) ≤ s.L :=
      Real.rpow_le_rpow_of_exponent_le hxone (by rw [hs]; linarith)
    exact a1.trans (le_mul_of_one_le_left (by linarith) hcm)
  have hp : (P.H.pde : ℝ) < s.X' := by
    rcases hOK.lev _ P.H.pde_level.1 with ⟨i, hi⟩ | h
    · exact absurd hi (P.H.pde_ne_g i).1
    · exact h
  have hp' : (P.H.pde' : ℝ) < s.X' := by
    rcases hOK.lev _ P.H.pde_level.2 with ⟨i, hi⟩ | h
    · exact absurd hi (P.H.pde_ne_g i).2
    · exact h
  refine GlobalTheory.Mem.LevelChoice.exists_levCh P du Ds _ hdu hDs hGam fun u => ?_
  have hT0 : 0 < (Ds / du u) ^ ((1 : ℝ) / (P.R.f * P.R.k)) * GamS C s P.R ^ (-(2 : ℝ) / (P.R.f * P.R.k)) := by
    have : (0 : ℝ) < du u := by exact_mod_cast hdu u
    have : 0 < GamS C s P.R := by linarith
    positivity
  obtain ⟨T, hT, hlo, hhi, hN⟩ := h1 s P.R P.H.condN P.H.d (P.H.g 0) (P.H.g 1) _ hs hx1 hOK.rank hOK.val.modRow
    (P.H.g_prime 0).one_le (P.H.g_prime 1).one_le (hg 0) (hg 1) hT0 (hwin u)
  have hXT : s.X' ≤ T :=
    hXL.trans (((Real.le_log_iff_exp_le hT0).1 (hwin u)).trans hlo)
  have hM : 1 ≤ P.H.QS * P.H.q * P.H.d * (P.H.g 0 * P.H.g 1) ^ 2 := by
    have hn : 0 < P.H.QS := P.H.QS_pos
    have hq : 0 < P.H.q := P.H.hyp.1.pos
    have hd : 0 < P.H.d := P.H.hyp.2.1.pos
    have h0 := (P.H.g_prime 0).pos
    have h1 := (P.H.g_prime 1).pos
    exact Nat.succ_le_of_lt (by positivity)
  obtain ⟨⟨π, hK, hπ, hc⟩, -⟩ := GlobalTheory.EX.normOne_host P.R P.H _ T hM hN
  refine ⟨π, T, hT, ?_, ?_, hK, hπ, hc, hlo, hhi⟩
  · rintro rfl; linarith
  · rintro rfl; linarith

end GlobalTheory.EX.OB
