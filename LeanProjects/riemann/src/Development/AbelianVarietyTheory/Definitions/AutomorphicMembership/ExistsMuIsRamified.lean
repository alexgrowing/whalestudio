import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsBaseJointFld
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpreadLamOfLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardDvdCardGL
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSmallPrimeOff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLevChOfLevelPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsStdLarge
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsFamPOfKits
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRanksRankValFrame
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MPowFiveMulFMulLLe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNumAt

noncomputable section

namespace GlobalTheory.Mem.Top.Inh

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

theorem g_big (eps : ℝ) (h0 : 0 < eps) (h1 : eps < 1 / 52) : ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (g : ℕ), s.eps = eps → x0 ≤ s.x →
    RankVal s R → ((R.k : ℝ) * s.b) ^ 8 ≤ g → 2 * R.f * R.k < g - 1 := by
  obtain ⟨x3, hx3⟩ := rank_basic_bounds eps h0 h1
  obtain ⟨x4, hx4⟩ := GlobalTheory.scale_poly_comparison eps 4 1 h0 one_pos
  refine ⟨max x3 (max x4 10), fun s R g he hx hR hg => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨y3, y4, y5⟩ := hx
  obtain ⟨hf, -⟩ := hx3 s R he y3 hR
  obtain ⟨-, -, hb, -⟩ := hx4 s he y4
  have hx0 : 0 < s.x := by linarith
  have hX1 : 1 ≤ s.X' := Real.one_le_exp (by positivity)
  have hk3 := R.m_add_three_le_k
  have pw : ∀ n : ℕ, s.x ^ (n : ℝ) = s.x ^ n := fun n => Real.rpow_natCast _ _
  have hf' : (R.f : ℝ) ≤ s.x ^ 3 := by rw [← pw]; exact_mod_cast hf
  have hb' : s.x ^ 4 ≤ s.b := by
    rw [Real.rpow_one] at hb
    rw [← pw]
    exact le_trans (by exact_mod_cast le_mul_of_one_le_right (by positivity) hX1) hb
  have h3 : 1 ≤ s.x ^ 3 := one_le_pow₀ (by linarith)
  have h4 : 10 * s.x ^ 3 ≤ s.b := by
    calc 10 * s.x ^ 3 ≤ s.x * s.x ^ 3 := mul_le_mul_of_nonneg_right y5 (by positivity)
      _ = s.x ^ 4 := by ring
      _ ≤ s.b := hb'
  have hk1 : (1 : ℝ) ≤ R.k := by exact_mod_cast (by omega : 1 ≤ R.k)
  have c1 : (R.k : ℝ) * s.b ≤ g :=
    (le_self_pow₀ (one_le_mul_of_one_le_of_one_le hk1 (by linarith)) (by norm_num)).trans hg
  have c3 : ((2 * R.f * R.k + 1 : ℕ) : ℝ) < g := by
    have d1 := mul_le_mul_of_nonneg_left h4 (show (0 : ℝ) ≤ R.k by positivity)
    have d2 := mul_le_mul_of_nonneg_left hf' (show (0 : ℝ) ≤ R.k by positivity)
    have d3 := one_le_mul_of_one_le_of_one_le hk1 h3
    push_cast
    nlinarith
  have c4 : 2 * R.f * R.k + 1 < g := by exact_mod_cast c3
  omega

set_option maxHeartbeats 1000000 in

theorem not_ev_false (hH : DC.HostExQ) (hLP : LevelPrime) (hSP : SmallPrimeOne) (h2b : StandardLattice.SiegelMassRatioCM) : ¬ Ev fun _ => False := by
  rintro ⟨ε0, hε0, h⟩
  have he : 0 < min ε0 (1 / 100) := lt_min hε0 (by norm_num)
  have he52 : min ε0 (1 / 100) < 1 / 52 := (min_le_right _ _).trans_lt (by norm_num)
  have hle := min_le_left ε0 (1 / 100)
  generalize min ε0 (1 / 100) = eps at he he52 hle
  obtain ⟨la, hla, hH⟩ := hH
  obtain ⟨CT2, C8, C5, c6, Cb, xH, h8, -, -, -, S, hH⟩ := hH eps he he52
  obtain ⟨K0, h⟩ := h eps C8 he hle he52 h8
  obtain ⟨C, hS, hCT, hCp, hL, -⟩ := GlobalTheory.EX.exists_std_large K0 K0 CT2 C8 h8
  obtain ⟨c1, h⟩ := h C hS hCp hL
  have hcD : 0 ≤ max c1 0 := le_max_right _ _
  obtain ⟨c2, h⟩ := h _ (le_max_left c1 0)
  generalize max c1 0 = cD at hcD h
  obtain ⟨c2', hlow⟩ := WinLow.window_lower h2b eps C he he52 hS cD hcD
  obtain ⟨ch, a1, a2, a3⟩ : ∃ ch : ℝ, c2 ≤ ch ∧ c2' ≤ ch ∧ 402 ≤ ch := ⟨max c2 (max c2' 402), by simp, by simp, by simp⟩
  obtain ⟨x0, h⟩ := h ch a1
  obtain ⟨x1, hlow⟩ := hlow ch a2
  have hmid := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCF : (0 : ℝ) ≤ C.P.CF := zero_le_one.trans (hmid _ (by simp [FC.cMid]))
  have hCG : (0 : ℝ) ≤ C.CGam := zero_le_one.trans (hmid _ (by simp [FC.cMid]))
  obtain ⟨xw, hw⟩ := exists_weights_in_windows eps C he he52 hS
  obtain ⟨xc, hc⟩ := exists_injective_words eps C.CGam C.P.CF he he52 hCG hCF
  obtain ⟨x2, h2⟩ := chOK_of_host hSP eps C5 c6 Cb cD ch C he he52 hS hcD a3
  obtain ⟨x3, h3⟩ := exists_levCh_of_levelPrime hLP eps 1 C he he52 one_pos hS
  obtain ⟨x4, h4⟩ := g_big eps he he52
  obtain ⟨s, hs, hx, hmem⟩ := S.exists_mem hla.le he he52
    (max x0 (max x1 (max x2 (max x3 (max x4 (max xH (max xw xc)))))))
  simp only [max_le_iff] at hx
  obtain ⟨b0, b1, b2, b3, b4, bH, bw, bc⟩ := hx
  obtain ⟨R, H, q0, hRV, hHT, hHG, -⟩ := hH s hs bH hmem
  obtain ⟨a, b, hab⟩ := hw s R H hs bw hRV
  obtain ⟨c, hci, -⟩ := hc s R hs bc hRV
  obtain ⟨H', q1, hcW, w0, k1, k2, k3, k4, k5, k6, k7, k8, hCh, -⟩ :=
    h2 s R H q0 a b _ c 0 hs b2 hRV (hHT.trans hCT.symm) (hCp ▸ hHG) hab rfl hci R.ord_pos
  choose du hpos hdu using fun u => DuInt.duStarOf_nat R H' (hcW u) (fun i => (k2 _ (H'.g_level i)).2)
    fun i => h4 s R _ hs b4 hRV (hCh.val.2.2.2.2.1 i).1
  obtain ⟨hD, hDle⟩ := DsLow.DsP_pos_and_lower (@PreCh.mk R H' k1 k2 k3 _ _ w0 hcW k4 k5 k6 k7 k8)
  obtain ⟨Lv, l1, l2, l3⟩ := h3 cD ch s _ q1 a b c du _ hs b3 hCh hpos hD fun u => by
    rw [one_mul]
    exact hlow s _ q1 a b c du _ hs b1 hCh hdu hDle u
  exact h ⟨s, C, cD, ch, _, q1, a, b, c, hS, hCh, Lv, fun u => by rw [l1]; exact hdu u, l2, l3⟩ rfl rfl rfl hs b0

end GlobalTheory.Mem.Top.Inh

end
