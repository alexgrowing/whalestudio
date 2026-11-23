import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Formalism.LocalToGlobal.Divisibility.ZscOfNum
import Formalism.SharpRestriction.ElevenLe
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GZeroLogBound

open Formalism.BasicNotions Formalism.MainNotions

noncomputable section

namespace Formalism.L2.DIV.Cons

open Formalism.L2.DIV

variable {D : D7}

theorem two_r_sq_le_b (L : SizeData₂ D) (hSC : SizeCond L) : 2 * (D.R.r : ℝ) ^ 2 ≤ L.sc.b := by
  have hq : (1 : ℝ) ≤ D.host.q := by exact_mod_cast D.host.hyp.1.one_lt.le
  have hd : (1 : ℝ) ≤ D.host.d := by exact_mod_cast D.host.hyp.2.1.one_lt.le
  have hn : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  have hc1 : (1 : ℝ) ≤ szCond L := by
    unfold szCond
    have h4 : (1 : ℝ) ≤ (D.host.QS : ℝ) := by exact_mod_cast D.host.QS_pos
    have h5 : (1 : ℝ) ≤ (D.host.QS : ℝ) * D.host.q := by nlinarith
    nlinarith
  have hrt : D.R.r + 5 ≤ D.R.t := by
    have := D.R.rank_add_five_le
    unfold Ranks.r
    omega
  have ht5 : (5 : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : 5 ≤ D.R.t)
  have hrt' : (D.R.r : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : D.R.r ≤ D.R.t)
  have ht0 : (0 : ℝ) ≤ D.R.t := by linarith
  have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _

  have hpow : (D.R.t : ℝ) ^ 150 ≤ Real.sqrt L.sc.b := by
    have h1 : (1 : ℝ) ≤ szCond L ^ 36 := one_le_pow₀ hc1
    have h2 : (0 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := pow_nonneg ht0 _
    have := hSC
    unfold SizeCond at this
    nlinarith

  have h2t : 2 * (D.R.t : ℝ) ^ 2 ≤ (D.R.t : ℝ) ^ 150 := by
    have h148 : (2 : ℝ) ≤ (D.R.t : ℝ) ^ 148 := by
      calc (2 : ℝ) ≤ 5 := by norm_num
        _ ≤ (D.R.t : ℝ) := ht5
        _ = (D.R.t : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (D.R.t : ℝ) ^ 148 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have : (D.R.t : ℝ) ^ 150 = (D.R.t : ℝ) ^ 2 * (D.R.t : ℝ) ^ 148 := by ring
    rw [this]
    nlinarith [pow_nonneg ht0 2]

  have hb1 : (1 : ℝ) ≤ L.sc.b := by
    unfold Scale.b
    exact Real.one_le_exp (by unfold Scale.L; exact Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _)
  have hsq : Real.sqrt L.sc.b ≤ L.sc.b := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hr2 : (D.R.r : ℝ) ^ 2 ≤ (D.R.t : ℝ) ^ 2 := pow_le_pow_left₀ hr0 hrt' 2
  linarith

theorem log_card_le_unitE {G : Type} [Fintype G] (L : SizeData₂ D) (hSG : SizeG L) (hSC : SizeCond L) (Del h0 : ℕ) (Nc : ℝ)
    (hNc : 0 ≤ Nc) (hc : Fintype.card G = D.what₂.restRowsFiniteGroupCard) :
    Real.log (Fintype.card G : ℝ) ≤ 2 * ((D.R.m : ℝ) * (ofRecord D L Del h0).unitE Nc) := by
  have hx1 : 1 ≤ L.sc.x := le_of_lt L.sc.one_lt_alt
  have hX1 : (1 : ℝ) ≤ L.sc.x ^ L.sc.eps := Real.one_le_rpow hx1 L.sc.eps_pos.le
  have hX0 : (0 : ℝ) ≤ L.sc.x ^ L.sc.eps := by linarith
  have hg0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos

  have hlam : Real.log (Fintype.card G : ℝ) ≤
      2 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * Real.log (2 * (D.host.g 0 : ℝ)) := by
    have h := GZeroLogBound D (D.host.g 0 : ℝ) (fun i => (hSG i 0).2.1)
    rw [hc]
    exact h

  have hth : L.sc.x ^ szTh L ≤ L.sc.x ^ L.sc.eps := by
    apply Real.rpow_le_rpow_of_exponent_le hx1
    unfold szTh
    linarith [L.sc.eps_pos]
  have hlg : Real.log (2 * (D.host.g 0 : ℝ)) ≤ 2 * (L.sc.x ^ L.sc.eps * L.sc.x ^ L.sc.eps) := by
    rw [Real.log_mul (by norm_num) hg0.ne']
    have h1 := (hSG 0 0).2.2
    have h2 : L.sc.x ^ szTh L * L.sc.L ≤ L.sc.x ^ L.sc.eps * L.sc.x ^ L.sc.eps := by
      show L.sc.x ^ szTh L * L.sc.x ^ L.sc.eps ≤ _
      exact mul_le_mul_of_nonneg_right hth hX0
    have h3 := Real.log_two_lt_d9
    have h4 : (1 : ℝ) ≤ L.sc.x ^ L.sc.eps * L.sc.x ^ L.sc.eps := by nlinarith
    linarith
  have hr := two_r_sq_le_b L hSC
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hm1 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have hr0 : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 2 := pow_nonneg (Nat.cast_nonneg _) 2
  have hb0 : (0 : ℝ) ≤ L.sc.b := by linarith
  set X := L.sc.x ^ L.sc.eps with hXdef

  have hU : (ofRecord D L Del h0).unitE Nc = X * ((D.R.f : ℝ) * D.R.m * L.sc.b * X + Nc) := rfl
  rw [hU]
  have hXX : (0 : ℝ) ≤ X * X := mul_nonneg hX0 hX0
  calc Real.log (Fintype.card G : ℝ)
      ≤ 2 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (2 * (X * X)) := by
        refine hlam.trans (mul_le_mul_of_nonneg_left hlg ?_)
        positivity
    _ = (D.R.f : ℝ) * (2 * (D.R.r : ℝ) ^ 2) * (2 * (X * X)) := by ring
    _ ≤ (D.R.f : ℝ) * ((D.R.m : ℝ) ^ 2 * L.sc.b) * (2 * (X * X)) := by
        have : 2 * (D.R.r : ℝ) ^ 2 ≤ (D.R.m : ℝ) ^ 2 * L.sc.b := by
          have hm2 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 2 := by nlinarith
          have := mul_le_mul_of_nonneg_right hm2 hb0
          linarith
        have h2 : (0 : ℝ) ≤ 2 * (X * X) := by positivity
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hf0) h2
    _ = 2 * ((D.R.m : ℝ) * (X * ((D.R.f : ℝ) * D.R.m * L.sc.b * X + 0))) := by ring
    _ ≤ 2 * ((D.R.m : ℝ) * (X * ((D.R.f : ℝ) * D.R.m * L.sc.b * X + Nc))) := by
        have hm0 : (0 : ℝ) ≤ D.R.m := by linarith
        gcongr

theorem lamSizeAt_record {G : Type} [Group G] [Fintype G] (L : SizeData₂ D) (hSG : SizeG L) (hSC : SizeCond L) (Del h0 : ℕ)
    (Nc : ℝ) (hNc : 0 ≤ Nc) (hc : Fintype.card G = D.what₂.restRowsFiniteGroupCard) (s : ℕ) (cs : ℝ)
    (hs : Real.log (s : ℝ) ≤ cs * ((D.R.m : ℝ) * (ofRecord D L Del h0).unitE Nc)) :
    LamSizeAt (G := G) (ofRecord D L Del h0) Nc s (2 + cs) := by
  have h1 := log_card_le_unitE (G := G) L hSG hSC Del h0 Nc hNc hc
  unfold LamSizeAt
  have key : (2 + cs) * ((D.R.m : ℝ) * (ofRecord D L Del h0).unitE Nc) =
      2 * ((D.R.m : ℝ) * (ofRecord D L Del h0).unitE Nc) + cs * ((D.R.m : ℝ) * (ofRecord D L Del h0).unitE Nc) := by
    ring
  show Real.log (Fintype.card G) + Real.log (s : ℝ) ≤ (2 + cs) * ((D.R.m : ℝ) * (ofRecord D L Del h0).unitE Nc)
  rw [key]
  linarith

theorem lamSizeAt_record_one {G : Type} [Group G] [Fintype G] (L : SizeData₂ D) (hSG : SizeG L) (hSC : SizeCond L)
    (Del h0 : ℕ) (Nc : ℝ) (hNc : 0 ≤ Nc) (hc : Fintype.card G = D.what₂.restRowsFiniteGroupCard) :
    LamSizeAt (G := G) (ofRecord D L Del h0) Nc 1 2 := by
  have h := lamSizeAt_record (G := G) L hSG hSC Del h0 Nc hNc hc 1 0 (by simp)
  have e : (2 : ℝ) + 0 = 2 := by norm_num
  rw [e] at h
  exact h

end Formalism.L2.DIV.Cons

end
