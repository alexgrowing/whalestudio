import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ThresholdBounds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SpectralTiesReal
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CfgTopFalseIff
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData

noncomputable section

open Finset NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.FourierDecayAlt

namespace Formalism.L2.SG.Pf.ThresholdAtPlaceBounds

theorem thrSet_pos {ι : Type} [Fintype ι] (G : Sz.Glob ι) {C : ℝ} (hC : 1 ≤ C) {de de' : ℕ → ℝ} {T T' : ℝ} {l : ℕ}
    (hB : ∀ w, 0 < G.supI de de' T T' l w) (hB1 : ∀ w, 0 < G.cutSupLong de de' T T' l w)
    (hka : 0 < G.ka) (hN : 0 < G.N) (hg : 0 < G.g) (hI : 0 < G.lenI) (hTT : 0 < T * T') :
    ∀ x ∈ G.thrSet C de de' T T' l, 0 < x := by
  intro x hx
  obtain ⟨i, -, -, hx⟩ := hx
  have hC0 : 0 < C := by linarith
  rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨s, -, -, rfl⟩ | rfl
  · refine Finset.prod_pos fun w _ => ?_
    have hw := hB1 w
    unfold Formalism.FourierDecayAlt.Sz.xHat
    positivity
  · refine Finset.prod_pos fun w _ => ?_
    have hw := hB w
    unfold Formalism.FourierDecayAlt.Sz.xHat
    positivity
  · refine Finset.prod_pos fun w _ => ?_
    have hw := hB w
    unfold Formalism.FourierDecayAlt.Sz.lamHat
    positivity
  · refine Finset.prod_pos fun w _ => ?_
    have hw := hB w
    have hs : 0 < Real.sqrt (T * T') := Real.sqrt_pos.mpr hTT
    unfold Formalism.FourierDecayAlt.Sz.lamPrimeHat
    apply Real.sqrt_pos.mpr
    positivity

variable {D : D7}

theorem gOf_place' (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (w : InfinitePlace D.host.E) :
    (Formalism.L2.SG.SpectralTiesReal.gOf D e).place w = Formalism.MainNotions.BridgeLemma.cfgOf D (e w) := by
  simp only [Formalism.FourierDecayAlt.Sz.Glob.place, Formalism.MainNotions.BridgeLemma.cfgOf, Formalism.L2.SG.SpectralTiesReal.gOf]
  congr 1
  exact Formalism.MainNotions.BridgeLemma.sza_m_eq D

theorem lOf_succ_le (de de' : ℕ → ℝ) : Formalism.L2.SG.SpectralTiesReal.lOf D de de' + 1 ≤ D.R.k := by
  unfold Formalism.L2.SG.SpectralTiesReal.lOf
  split_ifs with h
  · have := (Nat.find_spec h).2.1
    omega
  · have := D.R.m_add_three_le_k
    omega

theorem del_big {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (h5 : 5 ≤ Cl) :
    16000 * (D.R.k : ℝ) ^ 3 ≤ D.s.Del := by
  have hHc := hH
  obtain ⟨-, -, a3, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, a20, -, -, -, -, -⟩ := hHc
  have hk5 : (5 : ℝ) ≤ D.R.k := by exact_mod_cast Formalism.MainNotions.BridgeLemma.five_le_k D
  have hL := Formalism.MainNotions.BridgeLemma.one_le_L large₂
  have hf16 : (16 : ℝ) ≤ D.R.f := by
    have h2 := D.R.two_le_m
    have : 16 ≤ D.R.m ^ 4 := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ D.R.m ^ 4 := Nat.pow_le_pow_left h2 4
    exact_mod_cast le_trans this a3
  set x : ℝ := (D.R.k : ℝ) * D.R.f * large₂.sc.L with hx
  have hx1 : 1 ≤ x := by
    have : (1 : ℝ) * 1 * 1 ≤ (D.R.k : ℝ) * D.R.f * large₂.sc.L := by gcongr <;> linarith
    linarith
  have hp : x ^ (5 : ℝ) ≤ x ^ Cl := Real.rpow_le_rpow_of_exponent_le hx1 h5
  have e5 : x ^ (5 : ℝ) = x ^ (5 : ℕ) := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e5] at hp
  have hx5 : x ^ 5 = (D.R.k : ℝ) ^ 3 * ((D.R.k : ℝ) ^ 2 * (D.R.f : ℝ) ^ 5 * large₂.sc.L ^ 5) := by rw [hx]; ring
  have hf5 : (16 : ℝ) ^ 5 ≤ (D.R.f : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) hf16 5
  have hL5 : 1 ≤ large₂.sc.L ^ 5 := one_le_pow₀ hL
  have hk2 : (25 : ℝ) ≤ (D.R.k : ℝ) ^ 2 := by nlinarith
  have hprod : (16000 : ℝ) ≤ (D.R.k : ℝ) ^ 2 * (D.R.f : ℝ) ^ 5 * large₂.sc.L ^ 5 := by
    have a : (25 : ℝ) * 16 ^ 5 * 1 ≤ (D.R.k : ℝ) ^ 2 * (D.R.f : ℝ) ^ 5 * large₂.sc.L ^ 5 := by gcongr
    linarith
  have hk3 : 0 ≤ (D.R.k : ℝ) ^ 3 := by positivity
  have : 16000 * (D.R.k : ℝ) ^ 3 ≤ x ^ 5 := by rw [hx5]; nlinarith
  linarith

theorem first_size_lower_bound {large₂ : SizeData₂ D} {C0 C' Cl Cg cb Cu cT CT : ℝ} (hD : StandingNumericalData D C0) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (h40 : 40 ≤ Cl) (τ : D.what₂.Tau) :
    40 * ((Formalism.MainNotions.BridgeLemma.cfgOf D τ).m : ℝ) * (Formalism.MainNotions.BridgeLemma.cfgOf D τ).k * (Formalism.MainNotions.BridgeLemma.cfgOf D τ).Del ≤
      (Formalism.MainNotions.BridgeLemma.cfgOf D τ).b 1 := by
  obtain ⟨-, -, -, -, -, -, -, h8, -, -, -, -, -, -, -, h16, -⟩ := hH
  have hm := D.R.two_le_m
  have hk3 := D.R.m_add_three_le_k
  have h1m : (1 : ℕ) ≤ D.R.m := by omega
  have hb := h8 τ 1 le_rfl h1m
  have hkpos : (0 : ℝ) < (D.R.k : ℝ) := by exact_mod_cast (by omega : 0 < D.R.k)
  have hk : (0 : ℝ) < (D.R.k : ℝ) ^ Cl := Real.rpow_pos_of_pos hkpos _
  have hkb : (D.R.k : ℝ) ^ Cl ≤ bOne D τ 1 := le_trans (le_max_left _ _) (h16 τ 1 le_rfl h1m).1
  dsimp only [Formalism.MainNotions.BridgeLemma.cfgOf]
  rcases le_or_gt 0 ((D.R.m : ℝ) * D.R.k * D.s.Del) with h0 | h0
  · nlinarith
  · nlinarith

theorem thrSet_pos_at {large₂ : SizeData₂ D} {C0 C' Cl Cg cb Cu cT CT : ℝ} (hD : StandingNumericalData D C0)
    (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (h40 : 40 ≤ Cl) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) {CA : ℝ}
    (hCA : 1 ≤ CA) (u u' : D.what₂.Word) :
    ∀ x ∈ (Formalism.L2.SG.SpectralTiesReal.gOf D e).thrSet CA (Formalism.MainNotions.BridgeLemma.deOf D u) (Formalism.MainNotions.BridgeLemma.deOf D u')
      (D.mem u).A.T (D.mem u').A.T
      (Formalism.L2.SG.SpectralTiesReal.lOf D (Formalism.MainNotions.BridgeLemma.deOf D u) (Formalism.MainNotions.BridgeLemma.deOf D u')), 0 < x := by
  have hk5 : (5 : ℝ) ≤ D.R.k := by exact_mod_cast Formalism.MainNotions.BridgeLemma.five_le_k D
  have hDel := del_big hH (by linarith)
  have hHc := hH
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, a19, -, -, -, -, -, -⟩ := hHc
  have hT : ((D.mem u).A.T : ℝ) ≠ 0 := by exact_mod_cast (D.mem u).A.T_prime.ne_zero
  have hT' : ((D.mem u').A.T : ℝ) ≠ 0 := by exact_mod_cast (D.mem u').A.T_prime.ne_zero
  have hTp : (0 : ℝ) < (D.mem u).A.T := by exact_mod_cast (D.mem u).A.T_prime.pos
  have hTp' : (0 : ℝ) < (D.mem u').A.T := by exact_mod_cast (D.mem u').A.T_prime.pos
  have hka : 0 < (Formalism.L2.SG.SpectralTiesReal.gOf D e).ka := by
    show 0 < Real.pi / D.host.v
    exact div_pos Real.pi_pos (by linarith)
  have hg : 0 < (Formalism.L2.SG.SpectralTiesReal.gOf D e).g := by
    show 0 < ((D.host.g 0 : ℕ) : ℝ) * ((D.host.g 1 : ℕ) : ℝ)
    have a : (0 : ℝ) < ((D.host.g 0 : ℕ) : ℝ) := by exact_mod_cast (D.host.g_prime 0).pos
    have b : (0 : ℝ) < ((D.host.g 1 : ℕ) : ℝ) := by exact_mod_cast (D.host.g_prime 1).pos
    exact mul_pos a b
  have hrk : (D.R.rS : ℝ) + 1 ≤ D.R.k := by
    have h1 := Formalism.MainNotions.BridgeLemma.m_eq D
    have h2 := D.R.m_add_three_le_k
    exact_mod_cast (by omega : D.R.rS + 1 ≤ D.R.k)
  have hN : (Formalism.L2.SG.SpectralTiesReal.gOf D e).N = 4 * 5 * ((D.R.rS : ℝ) + 1) := rfl
  have hr0 : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
  have hN3 : (Formalism.L2.SG.SpectralTiesReal.gOf D e).N ^ 3 ≤ D.s.Del / 2 := by
    rw [hN]
    have : ((D.R.rS : ℝ) + 1) ^ 3 ≤ (D.R.k : ℝ) ^ 3 := pow_le_pow_left₀ (by linarith) hrk 3
    nlinarith
  have hN1 : (11 / 4 : ℝ) ≤ (Formalism.L2.SG.SpectralTiesReal.gOf D e).N ^ 3 := by
    rw [hN]
    have h20 : (20 : ℝ) ≤ 4 * 5 * ((D.R.rS : ℝ) + 1) := by nlinarith
    have := pow_le_pow_left₀ (by norm_num) h20 3
    norm_num at this
    linarith
  have hl := lOf_succ_le (D := D) (Formalism.MainNotions.BridgeLemma.deOf D u) (Formalism.MainNotions.BridgeLemma.deOf D u')
  have hk3 : (125 : ℝ) ≤ (D.R.k : ℝ) ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num) hk5 3
    norm_num at this
    linarith
  have hD11 : (11 / 2 : ℝ) ≤ D.s.Del := by nlinarith
  refine thrSet_pos _ hCA (fun w => ?_) (fun w => ?_) hka (by rw [hN]; positivity) hg ?_ (mul_pos hTp hTp')
  · unfold Sz.Glob.supI
    rw [gOf_place']
    exact ThresholdBounds.supI_pos _ (Formalism.MainNotions.BridgeLemma.cfg_ok hD hH (e w)) (first_size_lower_bound hD hH h40 (e w)) hD11
      (Formalism.MainNotions.BridgeLemma.isWord_deOf D u) (Formalism.MainNotions.BridgeLemma.isWord_deOf D u') hl hT hT' hka (pow_pos hg _)
  · unfold Sz.Glob.cutSupLong
    rw [gOf_place']
    exact ThresholdBounds.sSup_be_image_cutIntervalLong_pos _ (Formalism.MainNotions.BridgeLemma.cfg_ok hD hH (e w)) (first_size_lower_bound hD hH h40 (e w)) hN1 hN3
      (Formalism.MainNotions.BridgeLemma.isWord_deOf D u) (Formalism.MainNotions.BridgeLemma.isWord_deOf D u') hl hT hT' hka (pow_pos hg _)
  · show 0 < (D.s.Del : ℝ) / 2 - 5 / 2
    linarith

end Formalism.L2.SG.Pf.ThresholdAtPlaceBounds
