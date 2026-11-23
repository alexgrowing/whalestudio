import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.CombBound4Of
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PvsDimYPos
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank
import Formalism.LocalRingCardinality.FourthPowerRankLeNF

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D}

section J

variable {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData X ka wL wF}

theorem vEt_nonneg_comb4 {S : Scal B} {c : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ} {Qf : ∀ la, LocalPointData G la}
    (hB : CombBound4 G Qf S c nus) (la : HeightOneSpectrum (𝓞 B.KO)) (ζ : PtsG G la) : 0 ≤ vEt (Qf la) ζ := by
  unfold vEt
  split_ifs with hj
  · exact div_nonneg (EReal.toReal_nonneg (hB la ζ).1) (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  · exact le_rfl

theorem nu_le_comb4 {S : Scal B} {c : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ} {Qf : ∀ la, LocalPointData G la}
    (hj : j < D.R.m) (hB : CombBound4 G Qf S c nus) (la : HeightOneSpectrum (𝓞 B.KO)) (hTie : (Qf la).InTie S) (ζ : PtsG G la) :
    (Qf la).nu S ζ ≤ nus la + max 0 c * vEt (Qf la) ζ := by
  have hv := vEt_nonneg_comb4 hB la ζ
  have hm : c * vEt (Qf la) ζ ≤ max 0 c * vEt (Qf la) ζ := mul_le_mul_of_nonneg_right (le_max_right _ _) hv
  have h1 := (hB la ζ).2 ((hTie ζ).2.2.1 hj)
  rw [← EReal.coe_toReal (hTie ζ).1 (hTie ζ).2.1, EReal.coe_le_coe_iff] at h1
  have h2 : c / (2 * (G.iet : ℝ)) * (X.vAt la ((Qf la).y ζ) (X.inc _ G.et)).toReal = c * vEt (Qf la) ζ := by
    unfold vEt
    rw [if_pos hj]
    ring
  rw [h2] at h1
  unfold LocalPointData.nu
  linarith

theorem Net_nonneg_comb4 {S : Scal B} {c : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ} {Qf : ∀ la, LocalPointData G la}
    (hB : CombBound4 G Qf S c nus) (la : HeightOneSpectrum (𝓞 B.KO)) : 0 ≤ (Qf la).Net := by
  unfold LocalPointData.Net
  exact finsum_nonneg fun ζ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (EReal.toReal_nonneg (hB la ζ).1)

theorem rLa_nonneg_comb4 {S : Scal B} {c' : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ} {Qf : ∀ la, LocalPointData G la}
    (hB : CombBound4 G Qf S c' nus) (la : HeightOneSpectrum (𝓞 B.KO)) (CRm : ℝ) (T : ℕ) (c : ℝ) :
    0 ≤ rLa (Qf la) CRm T c := by
  unfold rLa
  have h1 : (0 : ℝ) ≤ (if j < D.R.m then (T : ℝ) * (max 0 c / (2 * (G.iet : ℝ))) * (Qf la).Net else 0) := by
    split_ifs with hj
    · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (div_nonneg (le_max_left _ _)
        (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))) (Net_nonneg_comb4 hB la)
    · exact le_rfl
  have h2 : (0 : ℝ) ≤ ((Qf la).Ila.toNat : ℝ) := Nat.cast_nonneg _
  exact add_nonneg (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (add_nonneg h2 h1)) (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)

end J

theorem lift_index_pow_four_le_degree {large₂ : SizeData₂ D} {C2 A2 : ℝ} (h : PageAt large₂ C2 A2) : (D.R.m : ℝ) ^ 4 ≤ (D.R.f : ℝ) := by
  obtain ⟨Q, PT, hS, -, -⟩ := h
  exact_mod_cast Formalism.BasicNotions.m_pow_four_le_f large₂ hS

theorem sixteen_le_rdE_of_parA {large₂ : SizeData₂ D} {CA : ℝ} (h : ParA large₂ CA) : 16 ≤ D.host.rdE := by
  have hr : 2 * (D.R.f : ℝ) * D.R.m ≤ D.host.rdE := h.2.2.2.2.2.2.2.2.2
  have hf' : (8 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast D.eight_le_f
  have hm' : (1 : ℝ) ≤ (D.R.m : ℝ) := by
    have : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
    exact_mod_cast this
  nlinarith

theorem floor_of_tieC {large₂ : SizeData₂ D} {K : KAdm} {H : KHyp} {Ch Ah Cq Aq C2 A2 CR CA : ℝ}
    (ht : TieC K H Ch Ah Cq Aq C2 A2 CR) (hp : ParA large₂ CA) :
    D.host.rdE ^ 2 / (4 * (D.R.f : ℝ)) ≤ WeightFamilies.RRv D CR := by
  have hr : 1 ≤ D.host.rdE := by linarith [sixteen_le_rdE_of_parA hp]
  obtain ⟨-, -, -, -, -, h4, -⟩ := ht
  rw [h4]
  unfold WeightFamilies.RRv
  have e : D.host.rdE ^ (7 : ℝ) = D.host.rdE ^ (7 : ℕ) := by exact_mod_cast Real.rpow_natCast D.host.rdE 7
  rw [e]
  have hf' : (8 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast D.eight_le_f
  have h27 : D.host.rdE ^ 2 ≤ D.host.rdE ^ 7 := pow_le_pow_right₀ hr (by norm_num)
  have h0 : 0 ≤ D.host.rdE ^ 2 := by positivity
  calc D.host.rdE ^ 2 / (4 * (D.R.f : ℝ)) ≤ D.host.rdE ^ 2 := div_le_self h0 (by linarith)
    _ ≤ D.host.rdE ^ 7 := h27

theorem tie_eqs {K : KAdm} {H : KHyp} {Ch Ah Cq Aq C2 A2 CR : ℝ} (ht : TieC K H Ch Ah Cq Aq C2 A2 CR) :
    H.Cc = C2 ∧ H.Ac = A2 ∧ H.CRc = CR :=
  ⟨ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1.trans ht.2.2.2.2.2.1.symm⟩

theorem g0fm3_le_of_dom {large₂ : SizeData₂ D} {K : KAdm} {H : KHyp} {Ch Ah Cq Aq C2 A2 CR : ℝ} {j nW : ℕ}
    (hPg : PageAt large₂ C2 A2) (ht : TieC K H Ch Ah Cq Aq C2 A2 CR) (hd : DomAt D large₂ j nW H.C1) :
    (g0 D : ℝ) * D.R.f * (D.R.m : ℝ) ^ 3 ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 := by
  have hC : 1000 ≤ C2 := ht.1 ▸ hd.1
  have hA : 12 ≤ A2 := ht.2.2.2.2.2.2.2.1
  have hZ1 : 1 ≤ zBase large₂ := WeightFamilies.one_le_zBase large₂
  have hZA : zBase large₂ ≤ zBase large₂ ^ A2 := by
    calc zBase large₂ = zBase large₂ ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ zBase large₂ ^ A2 := Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
  have hL : 1 ≤ large₂.sc.L := by
    unfold Scale.L; exact Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hfr : (D.R.f : ℝ) * D.R.r ≤ zBase large₂ := by
    unfold zBase
    exact le_mul_of_one_le_right (by positivity) hL
  have hm1 : (1 : ℝ) ≤ (D.R.m : ℝ) := by
    have : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
    exact_mod_cast this
  have hr1 : (1 : ℝ) ≤ (D.R.r : ℝ) := by
    have : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
    exact_mod_cast this
  have hm3 : (D.R.m : ℝ) ^ 3 ≤ (D.R.f : ℝ) :=
    le_trans (pow_le_pow_right₀ hm1 (by norm_num)) (lift_index_pow_four_le_degree hPg)
  have hg : (g0 D : ℝ) = 1250 * (D.R.r : ℝ) := by unfold g0; push_cast; norm_num
  have a1 : (D.R.r : ℝ) * D.R.f * (D.R.m : ℝ) ^ 3 ≤ ((D.R.f : ℝ) * D.R.r) ^ 2 := by
    calc (D.R.r : ℝ) * D.R.f * (D.R.m : ℝ) ^ 3 ≤ (D.R.r : ℝ) * D.R.f * D.R.f :=
          mul_le_mul_of_nonneg_left hm3 (by positivity)
      _ = (D.R.f : ℝ) ^ 2 * D.R.r * 1 := by ring
      _ ≤ (D.R.f : ℝ) ^ 2 * D.R.r * D.R.r := mul_le_mul_of_nonneg_left hr1 (by positivity)
      _ = ((D.R.f : ℝ) * D.R.r) ^ 2 := by ring
  have a2 : ((D.R.f : ℝ) * D.R.r) ^ 2 ≤ zBase large₂ ^ 2 := pow_le_pow_left₀ (by positivity) hfr 2
  have a3 : 1000 * zBase large₂ ≤ C2 * zBase large₂ ^ A2 := mul_le_mul hC hZA (by linarith) (by linarith)
  have a4 : (1000 * zBase large₂) ^ 2 ≤ (C2 * zBase large₂ ^ A2) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (by norm_num) (by linarith)) a3 2
  have a5 : 0 ≤ zBase large₂ ^ 2 := sq_nonneg _
  unfold WeightFamilies.PPv
  rw [hg]
  calc 1250 * (D.R.r : ℝ) * D.R.f * (D.R.m : ℝ) ^ 3 = 1250 * ((D.R.r : ℝ) * D.R.f * (D.R.m : ℝ) ^ 3) := by ring
    _ ≤ 1250 * zBase large₂ ^ 2 := by linarith
    _ ≤ (1000 * zBase large₂) ^ 2 := by rw [mul_pow]; linarith
    _ ≤ (C2 * zBase large₂ ^ A2) ^ 2 := a4

theorem g0fm3_le_of_list {j : ℕ} {large₂ : SizeData₂ D} {X : PJ D B P j} {K : KAdm} {H : KHyp} {Ch Ah Cq Aq C2 A2 CR Bx CT : ℝ}
    {S : Scal B} {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    (hH : HypC large₂ X H C2 A2 CR Bx CT S ka wL wF T nP nW h0 nus) (ht : TieC K H Ch Ah Cq Aq C2 A2 CR)
    (hPg : PageAt large₂ C2 A2) : (g0 D : ℝ) * D.R.f * (D.R.m : ℝ) ^ 3 ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hd⟩ := hH.2.1
  exact g0fm3_le_of_dom hPg ht hd

theorem pvs_core4 (A E Cd Q R δ lδ d D T c g₀ G PH Prw Pη Pd PO PD PQ RR L κ F' f r SS PP C k b m δ₂ q DF ρ ρ' : ℝ)
    (hR : 0 ≤ R) (hRδ : R * δ ≤ d) (hδ : 0 ≤ δ) (hlδ0 : 0 ≤ lδ) (hlδ : lδ ≤ Pd) (hD : 1 ≤ D) (hT : 1 ≤ T)
    (hG : 0 ≤ G) (hPrw : 1 / 2 ≤ Prw) (hPrwH : Prw ≤ PH) (hPη : 0 ≤ Pη) (hL : 0 ≤ L) (hκ : 0 ≤ κ)
    (hf : 1 ≤ f) (hk : 1 ≤ k) (hm : 1 ≤ m) (hmk : m ≤ k) (hb : 0 < b) (hδ₂ : 0 < δ₂) (hδ₂1 : δ₂ ≤ 1) (hq : 0 < q)
    (hRR : 1 ≤ RR) (hg : 1 ≤ g₀) (hρ'0 : 0 ≤ ρ')
    (h1 : 2 * A ≤ δ * lδ + 2 * SS + 8 / 3 * D * (D + 4) * δ * Prw * L
      + 2 * (D + 4) * (D + 1) * δ * (2 * G + 6 * PH) * L)
    (h2 : 2 * E ≤ T * c * (g₀ * ((D + 1) * δ * (2 * G + 6 * PH) * L + 4 / 3 * D * δ * Prw * L) + δ * Pη))
    (hSS : SS ≤ δ * (G * F')) (hF : F' ≤ (D + 2) * L + 5 * f * r ^ 2 * T) (hS2 : T * L ≤ 2 * κ)
    (hdeep : Cd ≤ ρ * (PD * κ)) (hquot : Q ≤ ρ' * PQ * κ)
    (hρ : ρ ≤ ρ' + 22 * D ^ 2 * d / T) (hρ' : ρ' ≤ 22 * D ^ 2 * d / T)
    (h25P : (2 * G + 6 * PH + Prw) * 25 ≤ PP) (hPηP : Pη ≤ PP) (hPDP : PD ≤ PP)
    (hPD : 3 / 2 * (Pd + PO) ≤ PD) (hPO : 19 * (f * r ^ 2) ≤ PO)
    (hP1 : 60 * G + 180 * PH + 44 * PD + 22 * PQ ≤ PP ^ 2 * D)
    (hCK : 4 * C ≤ PP ^ 2 * f) (hS1 : κ ≤ C * k * f * b) (hbκ : b ≤ κ)
    (hS5 : PP ^ 3 * T ^ 2 ≤ b) (hT3 : PP ^ 4 * D ^ 3 * k * f / (m * δ₂) ≤ T)
    (hc : c = RR * PP * DF ^ 2 / q) (hTc : T * c * g₀ ≤ 1) (hql : RR ^ 4 * PP ^ 3 * DF ^ 2 ≤ q) :
    R * (A + E) + Cd + Q ≤ d * f * m * b * δ₂ := by
  have hT0 : 0 < T := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hPH : 0 ≤ PH := by linarith
  have hd : 0 ≤ d := le_trans (mul_nonneg hR hδ) hRδ
  have hfr : 0 ≤ f * r ^ 2 := by positivity
  have hPd0 : 0 ≤ Pd := le_trans hlδ0 hlδ
  have hPO0 : 0 ≤ PO := le_trans (by positivity) hPO
  have hPD0 : 0 ≤ PD := le_trans (by positivity) hPD

  have hPP87 : 87 ≤ PP := by linarith
  have hPP0 : 0 < PP := by linarith
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hmδ : 0 < m * δ₂ := by positivity
  have hT3' : PP ^ 4 * D ^ 3 * k * f ≤ T * (m * δ₂) := by rwa [div_le_iff₀ hmδ] at hT3
  have hD3 : 1 ≤ D ^ 3 := one_le_pow₀ hD
  have hPPsq : 87 * PP ≤ PP ^ 2 := by
    have := mul_le_mul_of_nonneg_right hPP87 hPP0.le
    rw [sq]; exact this
  have hPP2 : 2 ≤ PP ^ 2 := by linarith
  have hPP24 : PP ^ 2 ≤ PP ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)

  obtain ⟨PQ', hPQ0, hPQle, hP1'⟩ : ∃ PQ' : ℝ, 0 ≤ PQ' ∧ PQ ≤ PQ' ∧
      60 * G + 180 * PH + 44 * PD + 22 * PQ' ≤ PP ^ 2 * D := by
    rcases le_total 0 PQ with h | h
    · exact ⟨PQ, h, le_rfl, hP1⟩
    · refine ⟨0, le_rfl, h, ?_⟩
      have := le_mul_of_one_le_right (by positivity : (0 : ℝ) ≤ PP ^ 2) hD
      linarith

  have lev := Formalism.MainNotions.Gaps.T0.levels_real A (2 * E) R δ d D T (T * c * g₀) c (Prw * L) G PH Pη L F' (f * r ^ 2)
    (4 / 3 * δ) (4 / 3 * (D + 4) * δ) ((D + 4) * (D + 1) * δ * (2 * G + 6 * PH) * L)
    ((D + 1) * δ * (2 * G + 6 * PH) * L) SS (G * F') lδ hR hRδ hδ hlδ0 hD0 hT0.le hc0 (by positivity) hTc
    (by positivity) (mul_le_mul_of_nonneg_right hPrwH hL) hG hPH hPη hL hfr
    (le_trans h1 (le_of_eq (by ring))) (le_trans h2 (le_of_eq (by ring))) hSS le_rfl
    (le_trans hF (le_of_eq (by ring))) le_rfl le_rfl le_rfl le_rfl

  have tn := Formalism.MainNotions.Gaps.T0.total_named_real d D T c G PH Pη Pd 0 0 0 RR T L κ (f * r ^ 2) lδ 0 0 hd hD hT hG hPH
    le_rfl le_rfl hκ hS2 hlδ0 hlδ (by rw [zero_add]; exact div_nonneg (mul_nonneg (by positivity) hd) hT0.le)
    (by rw [zero_mul, zero_div, mul_zero])

  have hDeep : Cd ≤ d * (44 * PD * D ^ 2 * κ / T) := by
    have hPDκ : 0 ≤ PD * κ := mul_nonneg hPD0 hκ
    have hρ44 : ρ ≤ 44 * D ^ 2 * d / T := by
      have e : 44 * D ^ 2 * d / T = 22 * D ^ 2 * d / T + 22 * D ^ 2 * d / T := by ring
      rw [e]; linarith
    have e2 : ρ * (PD * κ) ≤ 44 * D ^ 2 * d / T * (PD * κ) := mul_le_mul_of_nonneg_right hρ44 hPDκ
    have e3 : 44 * D ^ 2 * d / T * (PD * κ) = d * (44 * PD * D ^ 2 * κ / T) := by ring
    linarith

  have hQ' : Q ≤ d * (22 * PQ' * D ^ 2 * κ / T) := by
    have e1 : ρ' * PQ * κ ≤ ρ' * PQ' * κ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPQle hρ'0) hκ
    have e2 : ρ' * (PQ' * κ) ≤ 22 * D ^ 2 * d / T * (PQ' * κ) := mul_le_mul_of_nonneg_right hρ' (by positivity)
    have e3 : 22 * D ^ 2 * d / T * (PQ' * κ) = d * (22 * PQ' * D ^ 2 * κ / T) := by ring
    have e4 : ρ' * PQ' * κ = ρ' * (PQ' * κ) := by ring
    linarith

  have r1 : (60 * G + 180 * PH + 44 * PD + 22 * PQ') * D ^ 2 ≤ PP ^ 2 * D ^ 3 := by
    have a : 60 * G + 180 * PH + 44 * PD + 22 * PQ' ≤ PP ^ 2 * D := hP1'
    calc (60 * G + 180 * PH + 44 * PD + 22 * PQ') * D ^ 2 ≤ PP ^ 2 * D * D ^ 2 :=
          mul_le_mul_of_nonneg_right a (by positivity)
      _ = PP ^ 2 * D ^ 3 := by ring
  have r2 : 5 * G * (f * r ^ 2) + Pd ≤ PP ^ 3 := by
    have a1 : 50 * G ≤ PP := by linarith
    have a2 : 28 * (f * r ^ 2) ≤ PP := by linarith
    have a3 : Pd ≤ PP := by linarith
    have a4 : (50 * G) * (28 * (f * r ^ 2)) ≤ PP * PP := mul_le_mul a1 a2 (by positivity) hPP0.le
    have a5 : PP * PP * 87 ≤ PP ^ 3 := by
      have : PP ^ 3 = PP * PP * PP := by ring
      rw [this]; exact mul_le_mul_of_nonneg_left hPP87 (by positivity)
    have a6 : PP * PP = PP ^ 2 := by ring
    have a7 : (50 * G) * (28 * (f * r ^ 2)) = 280 * (5 * G * (f * r ^ 2)) := by ring
    linarith
  have r3 : Pη / 2 ≤ PP ^ 2 := by linarith
  have tp := Formalism.MainNotions.Gaps.T0.total_le_of_bounds d D T c RR T κ (60 * G + 180 * PH + 44 * PD + 22 * PQ')
    (5 * G * (f * r ^ 2) + Pd) (Pη / 2) 0 PP hd hT0 hc0 hκ hT0 r1 r2 r3 (by positivity)

  have hC0 : 0 ≤ C := by
    by_contra h
    have hkfb : 0 < k * f * b := by positivity
    have := mul_neg_of_neg_of_pos (not_le.mp h) hkfb
    have e : C * (k * f * b) = C * k * f * b := by ring
    linarith
  have hbase : PP ^ 2 * k ≤ T * (m * δ₂) := by
    have e1 : PP ^ 2 * k ≤ PP ^ 4 * D ^ 3 * k * f := by
      calc PP ^ 2 * k ≤ PP ^ 4 * k := by gcongr
        _ = PP ^ 4 * 1 * k * 1 := by ring
        _ ≤ PP ^ 4 * D ^ 3 * k * f := by gcongr
    exact le_trans e1 hT3'
  have hmδk : m * δ₂ ≤ k := by
    have := mul_le_mul_of_nonneg_left hδ₂1 (by linarith : (0 : ℝ) ≤ m)
    linarith
  have hTPP : PP ^ 2 ≤ T := by
    have : PP ^ 2 * k ≤ T * k := le_trans hbase (mul_le_mul_of_nonneg_left hmδk hT0.le)
    exact le_of_mul_le_mul_right this (by linarith)
  have ps0 : PP ^ 3 * T ≤ f * m * b * δ₂ / 4 := by
    have e4 : 4 ≤ T * (m * δ₂) := by
      have := le_mul_of_one_le_right (by positivity : (0 : ℝ) ≤ PP ^ 2) hk
      linarith
    have e5 : 4 ≤ T * (f * m * δ₂) := by
      have : T * (m * δ₂) ≤ T * (f * m * δ₂) := by
        have : m * δ₂ ≤ f * m * δ₂ := by
          have := mul_le_mul_of_nonneg_right hf hmδ.le
          linarith
        exact mul_le_mul_of_nonneg_left this hT0.le
      linarith
    have e6 : PP ^ 3 * T * 4 ≤ PP ^ 3 * T * (T * (f * m * δ₂)) := mul_le_mul_of_nonneg_left e5 (by positivity)
    have e7 : PP ^ 3 * T * (T * (f * m * δ₂)) = PP ^ 3 * T ^ 2 * (f * m * δ₂) := by ring
    have e8 : PP ^ 3 * T ^ 2 * (f * m * δ₂) ≤ b * (f * m * δ₂) := mul_le_mul_of_nonneg_right hS5 (by positivity)
    linarith
  have ps1 : 4 * C * PP ^ 2 * D ^ 3 * k / (m * δ₂) ≤ T := by
    refine le_trans ?_ hT3
    apply div_le_div_of_nonneg_right _ hmδ.le
    calc 4 * C * PP ^ 2 * D ^ 3 * k = (4 * C) * (PP ^ 2 * D ^ 3 * k) := by ring
      _ ≤ (PP ^ 2 * f) * (PP ^ 2 * D ^ 3 * k) := mul_le_mul_of_nonneg_right hCK (by positivity)
      _ = PP ^ 4 * D ^ 3 * k * f := by ring
  have pg := Formalism.LatticeBaseChangeAlt.four_term_sum_bound_of_parameters d PP D κ T c RR T C k f b m δ₂ q DF g₀ hd hT0 le_rfl hPP0 hD hRR hq hC0 (by linarith)
    (by linarith) hb.le (by linarith) hδ₂ hS1 ps0 ps1 hc hg hTc hql hTPP hPP2
  have e0 : R * (A + E) = R * (A + 1 / 2 * (2 * E)) := by ring
  have e2 : d * ((60 * G + 180 * PH + 44 * PD + 22 * PQ') * D ^ 2 * κ / T + (5 * G * (f * r ^ 2) + Pd) * T
        + Pη / 2 * T * c + 0 * (1 / T + RR ^ 2 * c) * κ / T) =
      d * ((60 * G + 180 * PH + 40 * 0) * D ^ 2 * κ / T + (5 * G * (f * r ^ 2) + Pd) * T + Pη / 2 * T * c
        + 0 * (0 + 0) * (1 / T + RR ^ 2 * c) * κ / T) + d * (44 * PD * D ^ 2 * κ / T)
        + d * (22 * PQ' * D ^ 2 * κ / T) := by ring
  have e3 : (0 : ℝ) * 0 * κ = 0 := by ring
  rw [e0]
  linarith

variable {j : ℕ}

theorem sumGP4 (large₂ : SizeData₂ D) (X : PJ D B P j) (h1 : 1 ≤ j) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR : ℝ)
    {ka wL wF : WeightFamilies.Wt D j} (T nP nW : ℕ) (h0 : ℝ)
    (hA : ParA large₂ H.CA) (hS : SetC large₂ X H.CK H.C1 H.A1 ka wL wF T nP nW h0) (h3 : H3 large₂ H C2 A2 CR 0 wL T)
    (h4 : H4 large₂ X H C2 A2 CR ka wL wF T nW)
    (G : GlobalFamilyData X ka wL wF) (Gc PH Prw Pet Pd : ℝ)
    (hth' : ∀ i, WeightFamilies.meanLogSup B (G.th' i) ≤ Gc * wF.size)
    (hlogd : Real.log (finrank B.KO (B.Cusp j ka) : ℝ) ≤ Pd)
    (hRδ : (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ) * G.del ≤ (X.rk ka (B.Mlat j ka) : ℕ))
    (hSh1 : (G.rz : ℝ) ≤ G.rq + 22 * (WeightFamilies.dimY D j : ℝ) ^ 2 * (X.rk ka (B.Mlat j ka) : ℕ) / T)
    (hSh2 : (G.rq : ℝ) ≤ 22 * (WeightFamilies.dimY D j : ℝ) ^ 2 * (X.rk ka (B.Mlat j ka) : ℕ) / T)
    (hP : PolyDom4 (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka)
    (Qf : ∀ la, LocalPointData G la) (hHt : Heights Qf Gc PH Prw Pet) :
    (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ) * ((∑' la, ((Qf la).Ila.toNat : ℝ) * X.lN la) +
        (if j < D.R.m then (T : ℝ) * (max 0 (cc D large₂ C2 A2 CR wL) / (2 * (G.iet : ℝ))) *
          ∑' la, (Qf la).Net * X.lN la else 0)) +
      G.rz * ((2 * Gc + Prw + WeightFamilies.PP0v D large₂ K.CL K.AL * (1 + Real.log ka.size) + 3 / 2 * (Pd + PO D large₂)) * ka.size) +
      2 * (G.rq : ℝ) * WeightFamilies.PPv D large₂ Cq Aq * ka.size ≤
      X.rk ka (B.Mlat j ka) * D.R.f * D.R.m * large₂.sc.b * large₂.de2 := by
  obtain ⟨-, -, -, -, -, -, -, hS1, -, -, -, -, -, -, -, -, -, hT0, -, h40, -⟩ := hS
  obtain ⟨hq1, hq2, hq3, -, -, hq6⟩ := h3
  rw [Real.rpow_zero, one_mul] at hq1 hq2 hq3
  obtain ⟨hbκ, hS2, hF, hS5, -⟩ := h4
  obtain ⟨-, hCR0, hG0, -, hPP0, -, -, -, -, hCK, h25P, hPetP, hPDP, hP1, hPrw, hPrwH, hPet0, -⟩ := hP
  obtain ⟨-, -, hh1, hh2⟩ := hHt
  have hq : (0 : ℝ) < qq D := by
    have : (0 : ℝ) ≤ ((WeightFamilies.dimY D j + 4) * DF wL : ℝ) := by positivity
    linarith

  have hkN := D.R.m_add_three_le_k
  have hmN := D.R.two_le_m
  have hfN : 1 ≤ D.R.f := by
    have h0 : 0 < D.R.toFrame.ord := D.R.toFrame.ord_pos
    have h1 : D.R.f = 2 * D.R.toFrame.ord := rfl
    omega
  have hf1 : (1 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast hfN
  have hk1 : (1 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hm1 : (1 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hmk : (D.R.m : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast (by omega : D.R.m ≤ D.R.k)
  have hg : (1 : ℝ) ≤ (g0 D : ℝ) := by
    have : 1 ≤ g0 D := by
      unfold g0 Ranks.r
      omega
    exact_mod_cast this
  have hD1 : (1 : ℝ) ≤ (WeightFamilies.dimY D j : ℝ) := by exact_mod_cast pvs_dimY_pos D h1
  have hT1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT0
  have hR1 : (1 : ℝ) ≤ (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ) := by
    have : 0 < Nat.choose (T - 1) (WeightFamilies.dimY D j) := Nat.choose_pos (by omega)
    exact_mod_cast this
  have hL1 : 1 ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hb : 0 < large₂.sc.b := Real.exp_pos _
  have hrd : 1 ≤ D.host.rdE := by
    have e1 : 2 * (D.R.f : ℝ) * D.R.m ≤ D.host.rdE := hA.2.2.2.2.2.2.2.2.2
    have e2 : (1 : ℝ) * 1 ≤ (D.R.f : ℝ) * D.R.m := mul_le_mul hf1 hm1 zero_le_one (by linarith)
    linarith
  have hRR : 1 ≤ WeightFamilies.RRv D CR := Real.one_le_rpow hrd hCR0
  have hPP : 0 ≤ WeightFamilies.PPv D large₂ C2 A2 := by linarith
  have hc0 : 0 ≤ cc D large₂ C2 A2 CR wL := by
    unfold cc
    have : 0 ≤ WeightFamilies.RRv D CR := by linarith
    positivity
  have hκ1 : 1 ≤ ka.size := WeightFamilies.Wt.one_le_size ka
  have hPPl : 0 ≤ WeightFamilies.PP0v D large₂ K.CL K.AL * (1 + Real.log ka.size) :=
    mul_nonneg hPP0 (by linarith [Real.log_nonneg hκ1])
  have hLs : 1 ≤ wL.size := WeightFamilies.Wt.one_le_size wL
  have hδ0 : (0 : ℝ) ≤ (G.del : ℝ) := Nat.cast_nonneg _
  have hPd0 : 0 ≤ Pd := le_trans (Real.log_natCast_nonneg _) hlogd
  have hlδ : Real.log (G.del : ℝ) ≤ Pd := by
    have e1 : (G.del : ℝ) ≤ (finrank B.KO (B.Cusp j ka) : ℝ) := by
      have a1 : (1 : ℝ) * G.del ≤ (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ) * G.del :=
        mul_le_mul_of_nonneg_right hR1 hδ0
      have a2 : X.rk ka (B.Mlat j ka) ≤ finrank B.KO (B.Cusp j ka) := Submodule.finrank_le _
      have a3 : (X.rk ka (B.Mlat j ka) : ℝ) ≤ (finrank B.KO (B.Cusp j ka) : ℝ) := by exact_mod_cast a2
      linarith
    rcases Nat.eq_zero_or_pos G.del with h | h
    · rw [h]; simpa using hPd0
    · exact le_trans (Real.log_le_log (by exact_mod_cast h) e1) hlogd
  have hSS : ∑ i, WeightFamilies.meanLogSup B (G.th' i) ≤ (G.del : ℝ) * (Gc * wF.size) := by
    calc ∑ i, WeightFamilies.meanLogSup B (G.th' i) ≤ ∑ _i : Fin G.del, Gc * wF.size :=
          Finset.sum_le_sum fun i _ => hth' i
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hPO : 19 * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2) ≤ PO D large₂ := by
    unfold PO
    have a : (0 : ℝ) ≤ 19 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 := by positivity
    have b1 := mul_le_mul_of_nonneg_left hL1 a
    have b2 : (0 : ℝ) ≤ 198 * (D.R.f : ℝ) ^ 2 * large₂.sc.L := by positivity
    linarith
  have hTc : (T : ℝ) * cc D large₂ C2 A2 CR wL * (g0 D : ℝ) ≤ 1 := by
    unfold cc
    rw [show (T : ℝ) * (WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 * (DF wL : ℝ) ^ 2 / (qq D : ℝ)) * (g0 D : ℝ) =
      ((T : ℝ) * g0 D * WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 * (DF wL : ℝ) ^ 2) / (qq D : ℝ) by ring]
    exact (div_le_one hq).2 hq2

  have hE : 2 * (if j < D.R.m then (T : ℝ) * (max 0 (cc D large₂ C2 A2 CR wL) / (2 * (G.iet : ℝ))) *
        ∑' la, (Qf la).Net * X.lN la else 0) ≤
      (T : ℝ) * cc D large₂ C2 A2 CR wL * ((g0 D : ℝ) * (((WeightFamilies.dimY D j : ℝ) + 1) * G.del * (2 * Gc + 6 * PH) * wL.size +
        4 / 3 * (WeightFamilies.dimY D j : ℝ) * G.del * Prw * wL.size) + G.del * Pet) := by
    have hTc0 : 0 ≤ (T : ℝ) * cc D large₂ C2 A2 CR wL := by positivity
    split_ifs with hj
    · rw [max_eq_right hc0]
      have := mul_le_mul_of_nonneg_left (hh2 hj).2 hTc0
      refine le_trans (le_of_eq ?_) this
      ring
    · have hPH0 : 0 ≤ PH := by linarith
      have hPrw0 : 0 ≤ Prw := by linarith
      have hL0 : 0 ≤ wL.size := by linarith
      rw [mul_zero]
      positivity
  exact pvs_core4 _ _ _ _ _ (G.del : ℝ) (Real.log (G.del : ℝ)) (X.rk ka (B.Mlat j ka) : ℝ) (WeightFamilies.dimY D j : ℝ) (T : ℝ)
    (cc D large₂ C2 A2 CR wL) (g0 D : ℝ) Gc PH Prw Pet Pd (PO D large₂)
    (2 * Gc + Prw + WeightFamilies.PP0v D large₂ K.CL K.AL * (1 + Real.log ka.size) + 3 / 2 * (Pd + PO D large₂)) (2 * WeightFamilies.PPv D large₂ Cq Aq) (WeightFamilies.RRv D CR)
    wL.size ka.size wF.size (D.R.f : ℝ) (D.R.r : ℝ) (∑ i, WeightFamilies.meanLogSup B (G.th' i)) (WeightFamilies.PPv D large₂ C2 A2) H.CK
    (D.R.k : ℝ) large₂.sc.b (D.R.m : ℝ) large₂.de2 (qq D : ℝ) (DF wL : ℝ) (G.rz : ℝ) (G.rq : ℝ)
    (by linarith) hRδ hδ0 (Real.log_natCast_nonneg _) hlδ hD1 hT1 hG0 hPrw hPrwH hPet0 (by linarith) (by linarith)
    hf1 hk1 hm1 hmk hb large₂.thickDensity_pos large₂.thickDensity_le_one hq hRR hg (Nat.cast_nonneg _) hh1 hE hSS hF hS2 le_rfl
    (le_of_eq (by ring)) hSh1 hSh2 h25P hPetP hPDP (by linarith) hPO hP1 hCK hS1 hbκ hS5 hq3 rfl hTc hq1

theorem sumGC4 (large₂ : SizeData₂ D) (X : PJ D B P j) (h1 : 1 ≤ j) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ)
    (S : Scal B) {ka wL wF : WeightFamilies.Wt D j} (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (hH : HypC large₂ X H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus)
    (G : GlobalFamilyData X ka wL wF) (Gc PH Prw Pet Pd : ℝ)
    (hth' : G.TiedTh S Gc) (hlogd : DeepLogD X ka Pd)
    (hRδ : ShareRd (D := D) (j := j) T G.del (X.rk ka (B.Mlat j ka)))
    (hSh1 : ShareRhoT (D := D) (j := j) T G.rz G.rq (X.rk ka (B.Mlat j ka)))
    (hSh2 : ShareRhoP (D := D) (j := j) T G.rq (X.rk ka (B.Mlat j ka)))
    (hP : PolyDom4 (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka)
    (Qf : ∀ la, LocalPointData G la) (hHt : Heights Qf Gc PH Prw Pet) :
    (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ) * ((∑' la, ((Qf la).Ila.toNat : ℝ) * X.lN la) +
        (if j < D.R.m then (T : ℝ) * (max 0 (cc D large₂ C2 A2 CR wL) / (2 * (G.iet : ℝ))) *
          ∑' la, (Qf la).Net * X.lN la else 0)) +
      G.rz * ((2 * Gc + Prw + WeightFamilies.PP0v D large₂ K.CL K.AL * (1 + Real.log ka.size) + 3 / 2 * (Pd + PO D large₂)) * ka.size) +
      2 * (G.rq : ℝ) * WeightFamilies.PPv D large₂ Cq Aq * ka.size ≤
      X.rk ka (B.Mlat j ka) * D.R.f * D.R.m * large₂.sc.b * large₂.de2 :=
  sumGP4 large₂ X h1 K H Ch Ah Cq Aq C2 A2 CR T nP nW h0 hH.1 hH.2.1 hH.2.2.2.2.2.1 hH.2.2.2.2.2.2.1 G Gc PH Prw Pet Pd
    (fun i => (hth' i).2) hlogd hRδ hSh1 hSh2 hP Qf hHt

end Formalism.MainNotions.Gaps.EtaleWeightGaps
