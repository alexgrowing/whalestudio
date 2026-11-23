import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.QuotientParamNonneg

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

theorem pvs_core (A E Cd Q R δ lδ d D T c g₀ G PH Prw Pη Pd PO PD PQ RR L κ F' f r SS PP C k b m δ₂ q DF ρ ρ' : ℝ)
    (hR : 0 ≤ R) (hRδ : R * δ ≤ d) (hδ : 0 ≤ δ) (hlδ0 : 0 ≤ lδ) (hlδ : lδ ≤ Pd) (hD : 1 ≤ D) (hT : 1 ≤ T)
    (hG : 0 ≤ G) (hPrw : 1 / 2 ≤ Prw) (hPrwH : Prw ≤ PH) (hPη : 0 ≤ Pη) (hL : 0 ≤ L) (hκ : 0 ≤ κ)
    (hf : 1 ≤ f) (hk : 1 ≤ k) (hm : 1 ≤ m) (hmk : m ≤ k) (hb : 0 < b) (hδ₂ : 0 < δ₂) (hδ₂1 : δ₂ ≤ 1) (hq : 0 < q)
    (hRR : 1 ≤ RR) (hg : 1 ≤ g₀) (hρ'0 : 0 ≤ ρ')
    (h1 : 2 * A ≤ δ * lδ + 2 * SS + 8 / 3 * D * (D + 4) * δ * Prw * L
      + 2 * (D + 4) * (D + 1) * δ * (2 * G + 6 * PH) * L)
    (h2 : 2 * E ≤ T * c * (g₀ * ((D + 1) * δ * (2 * G + 6 * PH) * L + 4 / 3 * D * δ * Prw * L) + δ * Pη))
    (hSS : SS ≤ δ * (G * F')) (hF : F' ≤ (D + 2) * L + 5 * f * r ^ 2 * T) (hS2 : T * L ≤ 2 * κ)
    (hdeep : Cd ≤ ρ * (PD * κ)) (hquot : Q ≤ ρ' * PQ * κ)
    (hρ : ρ ≤ 22 * D ^ 2 * d / T) (hρ' : ρ' ≤ 22 * D ^ 2 * d / T)
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

  have tn := Formalism.MainNotions.Gaps.T0.total_named_real d D T c G PH Pη Pd PD 0 0 RR T L κ (f * r ^ 2) lδ ρ 0 hd hD hT hG hPH
    hPD0 le_rfl hκ hS2 hlδ0 hlδ (by rw [zero_add]; exact hρ) (by rw [zero_mul, zero_div, mul_zero])

  have hQ' : Q ≤ d * (22 * PQ' * D ^ 2 * κ / T) := by
    have e1 : ρ' * PQ * κ ≤ ρ' * PQ' * κ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPQle hρ'0) hκ
    have e2 : ρ' * (PQ' * κ) ≤ 22 * D ^ 2 * d / T * (PQ' * κ) := mul_le_mul_of_nonneg_right hρ' (by positivity)
    have e3 : 22 * D ^ 2 * d / T * (PQ' * κ) = d * (22 * PQ' * D ^ 2 * κ / T) := by ring
    have e4 : ρ' * PQ' * κ = ρ' * (PQ' * κ) := by ring
    linarith

  have r1 : (60 * G + 180 * PH + 40 * PD + 22 * PQ') * D ^ 2 ≤ PP ^ 2 * D ^ 3 := by
    have a : 60 * G + 180 * PH + 40 * PD + 22 * PQ' ≤ PP ^ 2 * D := by linarith
    calc (60 * G + 180 * PH + 40 * PD + 22 * PQ') * D ^ 2 ≤ PP ^ 2 * D * D ^ 2 :=
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
  have tp := Formalism.MainNotions.Gaps.T0.total_le_of_bounds d D T c RR T κ (60 * G + 180 * PH + 40 * PD + 22 * PQ')
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
  have e1 : ρ * (PD * κ) = ρ * PD * κ := by ring
  have e2 : d * ((60 * G + 180 * PH + 40 * PD + 22 * PQ') * D ^ 2 * κ / T + (5 * G * (f * r ^ 2) + Pd) * T
        + Pη / 2 * T * c + 0 * (1 / T + RR ^ 2 * c) * κ / T) =
      d * ((60 * G + 180 * PH + 40 * PD) * D ^ 2 * κ / T + (5 * G * (f * r ^ 2) + Pd) * T + Pη / 2 * T * c
        + 0 * (PD + 0) * (1 / T + RR ^ 2 * c) * κ / T) + d * (22 * PQ' * D ^ 2 * κ / T) := by ring
  have e3 : (0 : ℝ) * 0 * κ = 0 := by ring
  rw [e0]
  linarith

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem pvs_dimY_pos (D : D7) {j : ℕ} (h1 : 1 ≤ j) : 1 ≤ WeightFamilies.dimY D j := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hf : 1 ≤ D.R.f := by
    have h0 : 0 < D.R.n := D.R.toFrame.ord_pos
    have h2 : D.R.f = 2 * D.R.n := rfl
    omega
  have hp : 3 ≤ (D.R.sigW j).1 := by
    show 3 ≤ D.R.k + j - 1
    omega
  have h2 : 1 ≤ (D.R.sigW j).1 * ((D.R.sigW j).1 - 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    exact Nat.mul_le_mul (by omega) (by omega)
  unfold WeightFamilies.dimY
  exact Nat.mul_pos hf (by omega)

theorem sumGP (large₂ : SizeData₂ D) (X : PJ D B P j) (h1 : 1 ≤ j) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR : ℝ)
    {ka wL wF : WeightFamilies.Wt D j} (T nP nW : ℕ) (h0 : ℝ)
    (hA : ParA large₂ H.CA) (hS : SetC large₂ X H.CK H.C1 H.A1 ka wL wF T nP nW h0) (h3 : H3 large₂ H C2 A2 CR 0 wL T)
    (h4 : H4 large₂ X H C2 A2 CR ka wL wF T nW)
    (G : GlobalFamilyData X ka wL wF) (Gc PH Prw Pet Pd : ℝ)
    (hth' : ∀ i, WeightFamilies.meanLogSup B (G.th' i) ≤ Gc * wF.size)
    (hlogd : Real.log (finrank B.KO (B.Cusp j ka) : ℝ) ≤ Pd)
    (hRδ : (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ) * G.del ≤ (X.rk ka (B.Mlat j ka) : ℕ))
    (hSh1 : (G.rz : ℝ) ≤ 22 * (WeightFamilies.dimY D j : ℝ) ^ 2 * (X.rk ka (B.Mlat j ka) : ℕ) / T)
    (hSh2 : (G.rq : ℝ) ≤ 22 * (WeightFamilies.dimY D j : ℝ) ^ 2 * (X.rk ka (B.Mlat j ka) : ℕ) / T)
    (hP : PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka)
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
    have h0 : 0 < D.R.n := D.R.toFrame.ord_pos
    have h2 : D.R.f = 2 * D.R.n := rfl
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
  exact pvs_core _ _ _ _ _ (G.del : ℝ) (Real.log (G.del : ℝ)) (X.rk ka (B.Mlat j ka) : ℝ) (WeightFamilies.dimY D j : ℝ) (T : ℝ)
    (cc D large₂ C2 A2 CR wL) (g0 D : ℝ) Gc PH Prw Pet Pd (PO D large₂)
    (2 * Gc + Prw + WeightFamilies.PP0v D large₂ K.CL K.AL * (1 + Real.log ka.size) + 3 / 2 * (Pd + PO D large₂)) (2 * WeightFamilies.PPv D large₂ Cq Aq) (WeightFamilies.RRv D CR)
    wL.size ka.size wF.size (D.R.f : ℝ) (D.R.r : ℝ) (∑ i, WeightFamilies.meanLogSup B (G.th' i)) (WeightFamilies.PPv D large₂ C2 A2) H.CK
    (D.R.k : ℝ) large₂.sc.b (D.R.m : ℝ) large₂.de2 (qq D : ℝ) (DF wL : ℝ) (G.rz : ℝ) (G.rq : ℝ)
    (by linarith) hRδ hδ0 (Real.log_natCast_nonneg _) hlδ hD1 hT1 hG0 hPrw hPrwH hPet0 (by linarith) (by linarith)
    hf1 hk1 hm1 hmk hb large₂.thickDensity_pos large₂.thickDensity_le_one hq hRR hg (Nat.cast_nonneg _) hh1 hE hSS hF hS2 le_rfl
    (le_of_eq (by ring)) hSh1 hSh2 h25P hPetP hPDP (by linarith) hPO hP1 hCK hS1 hbκ hS5 hq3 rfl hTc hq1

theorem sumG (large₂ : SizeData₂ D) (X : PJ D B P j) (h1 : 1 ≤ j) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ)
    (S : Scal B) {ka wL wF : WeightFamilies.Wt D j} (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (hH : Hyp large₂ X H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus)
    (G : GlobalFamilyData X ka wL wF) (Gc PH Prw Pet Pd : ℝ)
    (hT : G.Tied large₂ S K.CRm T (cc D large₂ C2 A2 CR wL) Gc Prw Ch Ah K.Cf K.Af)
    (hI : DeepIn X ka large₂ K.CG K.AG Pd)
    (hSh : Shares D wL G.del G.rz G.rq (X.rk ka (B.Mlat j ka)) T K.CRm (cc D large₂ C2 A2 CR wL))
    (hP : PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka)
    (Qf : ∀ la, LocalPointData G la) (hHt : Heights Qf Gc PH Prw Pet) :
    (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ) * ((∑' la, ((Qf la).Ila.toNat : ℝ) * X.lN la) +
        (if j < D.R.m then (T : ℝ) * (max 0 (cc D large₂ C2 A2 CR wL) / (2 * (G.iet : ℝ))) *
          ∑' la, (Qf la).Net * X.lN la else 0)) +
      G.rz * ((2 * Gc + Prw + WeightFamilies.PP0v D large₂ K.CL K.AL * (1 + Real.log ka.size) + 3 / 2 * (Pd + PO D large₂)) * ka.size) +
      2 * (G.rq : ℝ) * WeightFamilies.PPv D large₂ Cq Aq * ka.size ≤
      X.rk ka (B.Mlat j ka) * D.R.f * D.R.m * large₂.sc.b * large₂.de2 :=
  sumGP large₂ X h1 K H Ch Ah Cq Aq C2 A2 CR T nP nW h0 hH.1 hH.2.1 hH.2.2.2.2.2.1 hH.2.2.2.2.2.2.1 G Gc PH Prw Pet Pd
    (fun i => (hT.2.2.2.2.2.1 i).2) hI.2.2.1 hSh.1 hSh.2.1 hSh.2.2 hP Qf hHt

theorem sumGC (large₂ : SizeData₂ D) (X : PJ D B P j) (h1 : 1 ≤ j) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ)
    (S : Scal B) {ka wL wF : WeightFamilies.Wt D j} (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (hH : HypC large₂ X H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus)
    (G : GlobalFamilyData X ka wL wF) (Gc PH Prw Pet Pd : ℝ)
    (hth' : G.TiedTh S Gc) (hlogd : DeepLogD X ka Pd)
    (hRδ : ShareRd (D := D) (j := j) T G.del (X.rk ka (B.Mlat j ka)))
    (hSh1 : ShareRho (D := D) (j := j) T G.rz (X.rk ka (B.Mlat j ka)))
    (hSh2 : ShareRhoP (D := D) (j := j) T G.rq (X.rk ka (B.Mlat j ka)))
    (hP : PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka)
    (Qf : ∀ la, LocalPointData G la) (hHt : Heights Qf Gc PH Prw Pet) :
    (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ) * ((∑' la, ((Qf la).Ila.toNat : ℝ) * X.lN la) +
        (if j < D.R.m then (T : ℝ) * (max 0 (cc D large₂ C2 A2 CR wL) / (2 * (G.iet : ℝ))) *
          ∑' la, (Qf la).Net * X.lN la else 0)) +
      G.rz * ((2 * Gc + Prw + WeightFamilies.PP0v D large₂ K.CL K.AL * (1 + Real.log ka.size) + 3 / 2 * (Pd + PO D large₂)) * ka.size) +
      2 * (G.rq : ℝ) * WeightFamilies.PPv D large₂ Cq Aq * ka.size ≤
      X.rk ka (B.Mlat j ka) * D.R.f * D.R.m * large₂.sc.b * large₂.de2 :=
  sumGP large₂ X h1 K H Ch Ah Cq Aq C2 A2 CR T nP nW h0 hH.1 hH.2.1 hH.2.2.2.2.2.1 hH.2.2.2.2.2.2.1 G Gc PH Prw Pet Pd
    (fun i => (hth' i).2) hlogd hRδ hSh1 hSh2 hP Qf hHt

end Formalism.MainNotions.Gaps.EtaleWeightGaps
