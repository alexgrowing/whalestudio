import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightSWith
import Formalism.LocalRingCardinality.SpanPowerMembership.FmZeroHLatEmpty
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt.SpreadBound

theorem spread_lamOf_le {R : Ranks} (p : HCParam R) (j : ℕ) (hj : j ≤ R.m) (hk : 0 < R.k) (hm : R.m - 1 < R.m) :
    (((Formalism.BasicNotions.Examples₂.lamOf p j).spread : ℤ) : ℚ) ≤ p.u ⟨0, hk⟩ + p.e ⟨R.m - 1, hm⟩ + R.N R.m := by
  have hN : 0 < R.N j := by unfold Ranks.N; omega
  have hNm := Formalism.BasicNotions.Examples₂.N_mono (R := R) hj
  have h2 := R.two_le_m
  unfold DomWeight.spread
  rw [dif_pos hN]
  push_cast
  rw [Formalism.BasicNotions.Examples₂.lamOf_eq p j hj, Formalism.BasicNotions.Examples₂.lamOf_eq p j hj, Formalism.BasicNotions.Examples₂.wtQ_eq_wtN, Formalism.BasicNotions.Examples₂.wtQ_eq_wtN]
  have a1 : Formalism.BasicNotions.Examples₂.wtN p (R.N R.m - 1) ≤ Formalism.BasicNotions.Examples₂.wtN p (R.N j - 1) :=
    Formalism.BasicNotions.Examples₂.wtN_anti p (by omega) (by omega)
  have hmul : R.m * (R.t + 1) = (R.m - 1) * (R.t + 1) + (R.t + 1) := by
    obtain ⟨n, hn⟩ : ∃ n, R.m = n + 1 := ⟨R.m - 1, by omega⟩
    rw [hn, Nat.add_sub_cancel]; ring
  have hb : Formalism.BasicNotions.Examples₂.blkN R (R.N R.m - 1) = R.m - 1 := by
    unfold Formalism.BasicNotions.Examples₂.blkN Ranks.N
    have : R.k + R.m * (R.t + 1) - 1 - R.k = R.t + (R.t + 1) * (R.m - 1) := by
      rw [hmul, mul_comm (R.t + 1)]; omega
    rw [this, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega), zero_add]
  have a2 : -p.e ⟨R.m - 1, hm⟩ ≤ Formalism.BasicNotions.Examples₂.wtN p (R.N R.m - 1) := by
    have c1 : ¬ R.N R.m - 1 < R.k := by unfold Ranks.N; omega
    have c2 : Formalism.BasicNotions.Examples₂.blkN R (R.N R.m - 1) < R.m := by omega
    unfold Formalism.BasicNotions.Examples₂.wtN
    rw [dif_neg c1, dif_pos c2]
    have e : (⟨Formalism.BasicNotions.Examples₂.blkN R (R.N R.m - 1), c2⟩ : Fin R.m) = ⟨R.m - 1, hm⟩ := Fin.ext hb
    rw [e]
    unfold wG
    push_cast
    have : (0 : ℚ) ≤ (2 * ((Formalism.BasicNotions.Examples₂.blkN R (R.N R.m - 1) : ℚ) + 1) - 1) * ((R.t : ℚ) + 1) / 2 := by
      have : (0 : ℚ) ≤ 2 * ((Formalism.BasicNotions.Examples₂.blkN R (R.N R.m - 1) : ℚ) + 1) - 1 := by
        have : (0 : ℚ) ≤ (Formalism.BasicNotions.Examples₂.blkN R (R.N R.m - 1) : ℚ) := by positivity
        linarith
      positivity
    have : (0 : ℚ) ≤ (R.k : ℚ) / 2 := by positivity
    linarith
  have a3 : Formalism.BasicNotions.Examples₂.wtN p 0 ≤ p.u ⟨0, hk⟩ := by
    unfold Formalism.BasicNotions.Examples₂.wtN
    rw [dif_pos hk]
    unfold hcToWeightQ rhoVec
    have : (1 : ℚ) ≤ R.k := by exact_mod_cast hk
    simp only [Nat.cast_zero]
    linarith
  have a4 : (R.N j : ℚ) ≤ R.N R.m := by exact_mod_cast hNm
  simp only
  linarith

end GlobalTheory.CoreHt.SpreadBound

namespace GlobalTheory.CoreHt.SpreadBound

theorem spread_lamTrue_le : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (L : SizeData₂ (I.rec7 l Z)) (CY : ℝ), HtRowsS L CY → 8 ≤ L.sc.X' → 2 ≤ L.sc.x → ∀ (u : B.Word) (j : ℕ), j ≤ B.R.m → ∀ τ,
    ((B.wts.lamTrue u j τ).spread : ℝ) ≤ 2 * L.sc.a := by
  intro B X I _ l Z L CY hS hX hx u j hj τ
  obtain ⟨⟨P⟩, -, -, ⟨hN3, -, hmt, hkS, hbT⟩, -, hT⟩ := hS
  have hm := B.R.two_le_m
  have hk : 5 ≤ B.R.k := by have := B.R.m_add_three_le_k; omega
  have hk0 : 0 < B.R.k := by omega
  have hm1 : B.R.m - 1 < B.R.m := by omega
  have c1 := spread_lamOf_le (B.hcW u τ) j hj hk0 hm1
  have c2 : (((B.wts.lamTrue u j τ).spread : ℤ) : ℝ) ≤
      (((B.hcW u τ).u ⟨0, hk0⟩ : ℚ) : ℝ) + (((B.hcW u τ).e ⟨B.R.m - 1, hm1⟩ : ℚ) : ℝ) + B.R.N B.R.m := by
    unfold Wts.lamTrue
    rw [spread_shiftW]
    exact_mod_cast c1
  refine c2.trans ?_
  have hx1 := L.sc.one_lt_alt
  have hL1 : 1 ≤ L.sc.L := Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp (by linarith)
  have ha : L.sc.a = L.sc.x * L.sc.b := rfl
  have hb2 : 2 * L.sc.b ≤ L.sc.a := by rw [ha]; nlinarith
  have hX0 : 0 < L.sc.X' := by linarith
  have hb'a : L.sc.b' ≤ L.sc.a / 8 := by
    have : 0 < L.sc.a := by linarith
    exact div_le_div_of_nonneg_left this.le (by norm_num) hX
  have hb'0 : 0 < L.sc.b' := by
    have : 0 < L.sc.a := by linarith
    exact div_pos this hX0
  have hn1 : (1 : ℝ) ≤ (I.rec7 l Z).R.n := by
    have : 1 ≤ (I.rec7 l Z).R.n := by unfold Ranks.n; exact Nat.succ_le_of_lt (by positivity)
    exact_mod_cast this
  have hw : L.sc.w'' (I.rec7 l Z).R.n ≤ L.sc.b' :=
    div_le_self hb'0.le (one_le_mul_of_one_le_of_one_le hx1.le hn1)
  have he := L.etaSz_pos
  have hS0 := L.Sc_pos
  have hm' : (2 : ℝ) ≤ B.R.m := by exact_mod_cast hm
  have hk' : (5 : ℝ) ≤ B.R.k := by exact_mod_cast hk
  have ht : (0 : ℝ) ≤ B.R.t := Nat.cast_nonneg _
  have heta : 2 * L.etaSz ≤ L.sc.b' := by
    have h1 : (2 : ℝ) ≤ B.R.m * ((B.R.t : ℝ) + 1) := by nlinarith
    have h2 := mul_le_mul_of_nonneg_right h1 he.le
    have h3 : (B.R.m : ℝ) * ((B.R.t : ℝ) + 1) * L.etaSz ≤ L.sc.w'' (I.rec7 l Z).R.n := hmt
    linarith
  have hSc : 5 * L.Sc ≤ L.sc.b' := by
    have h3 : (B.R.k : ℝ) * L.Sc ≤ L.sc.w'' (I.rec7 l Z).R.n := hkS
    nlinarith
  have hN1 : (1 : ℝ) ≤ B.R.N B.R.m := by
    have : 1 ≤ B.R.N B.R.m := by unfold Ranks.N; omega
    exact_mod_cast this
  have hNeta : (B.R.N B.R.m : ℝ) ≤ L.etaSz := by
    have h3 : 4 * (B.R.N B.R.m : ℝ) ^ 3 ≤ L.etaSz := hN3
    have h4 : (B.R.N B.R.m : ℝ) ^ 1 ≤ (B.R.N B.R.m : ℝ) ^ 3 := pow_le_pow_right₀ hN1 (by norm_num)
    rw [pow_one] at h4
    linarith
  have hkN : (B.R.k : ℝ) ≤ B.R.N B.R.m := by
    have : B.R.k ≤ B.R.N B.R.m := by unfold Ranks.N; omega
    exact_mod_cast this
  have hu0 : (B.hcW u τ).u ⟨0, hk0⟩ = ((I.rec7 l Z).hc τ).u ⟨0, hk0⟩ := (I.rec7 l Z).hcW_first u τ hk0
  have he0 : (B.hcW u τ).e = ((I.rec7 l Z).hc τ).e := (I.rec7 l Z).hcW_e u τ
  have hwm : wj (I.rec7 l Z) B.R.m τ = (((B.hcW u τ).e ⟨B.R.m - 1, hm1⟩ : ℚ) : ℝ) := by
    unfold wj
    rw [dif_pos (show B.R.m - 1 < (I.rec7 l Z).R.m from hm1)]
    exact (congrArg (fun f => ((f ⟨B.R.m - 1, hm1⟩ : ℚ) : ℝ)) he0).symm
  rw [← hwm, hu0]
  by_cases htop : ((I.rec7 l Z).eTau τ : (I.rec7 l Z).R.GG) ∈ (I.rec7 l Z).host.topPlaces
  · obtain ⟨t, htt⟩ : ∃ t : (I.rec7 l Z).host.TT,
        ((I.rec7 l Z).eTau τ : (I.rec7 l Z).R.GG) = (I.rec7 l Z).R.tau1 t := by
      unfold Host.topPlaces at htop
      obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 htop
      exact ⟨⟨t, ht⟩, hte.symm⟩
    rw [(L.top_u τ t hk0 htt).1]
    show (L.aT t : ℝ) + ((B.R.k : ℝ) - 1) / 2 + wj (I.rec7 l Z) B.R.m τ + (B.R.N B.R.m : ℝ) ≤ 2 * L.sc.a
    have a1 : wj (I.rec7 l Z) B.R.m τ ≤ (L.bT t : ℝ) + L.sc.b' / L.sc.x + L.etaSz :=
      (L.win_top B.R.m (by omega) le_rfl τ t htt).2
    have a2 : (L.aT t : ℝ) ≤ L.sc.a + L.sc.a / ((B.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) := (L.aT_win t).2
    have a3 : (5 : ℝ) ≤ (B.R.k : ℝ) * L.sc.x ^ (Scale.A / 2) :=
      hk'.trans (le_mul_of_one_le_right (by linarith) (Real.one_le_rpow hx1.le (by unfold Scale.A; norm_num)))
    have a4 : L.sc.a / ((B.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a / 5 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) a3
    have a5 : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'0.le hx1.le
    have a6 := hbT t
    linarith
  · have h1 := P.cloud_place_bound τ (by show 0 < B.R.k - 1; omega) htop
    have h2 := (L.cloud_v τ ⟨0, by show 0 < B.R.k - 1; omega⟩).2
    push_cast at h1
    by_cases hc : ((I.rec7 l Z).eTau τ : (I.rec7 l Z).R.GG) ∈ (I.rec7 l Z).host.thickPlaces
    · have a1 := hT B.R.m (by omega) le_rfl τ hc
      linarith
    · have a1 := (L.win_thin B.R.m (by omega) le_rfl τ ⟨((I.rec7 l Z).eTau τ).2, htop, hc⟩).2
      linarith

end GlobalTheory.CoreHt.SpreadBound
