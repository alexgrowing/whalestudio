import Formalism.SharpRestriction.Divisibility.SlopeExcess.ConstRankBaseLePolyFourth
import Formalism.SharpRestriction.GrowthBounds.TopChoiceBounds
import Formalism.SharpRestriction.GrowthBounds.JointsLit
import Formalism.SharpRestriction.GrowthBounds.AdmissibleIntegers.FirstTermSizeBound
import Formalism.LocalRingCardinality.DataExtra
import Formalism.SharpRestriction.Divisibility.HookProducts.CardLiftsEq

noncomputable section

namespace Formalism.MainNotions.DIV.HookProducts.HookProductWeightBounds

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.DIV.Proofs.HHParts

variable {D : D7} {L : SizeData₂ D}

def gC (L : SizeData₂ D) (C : ℝ) (p : ℕ) : ℝ := if (p : ℝ) ≤ L.sc.X'' D.R.n then C / (p : ℝ) else 0

theorem gC_nonneg (L : SizeData₂ D) {C : ℝ} (hC : 0 ≤ C) (p : ℕ) : 0 ≤ gC L C p := by
  unfold gC
  split_ifs
  · exact div_nonneg hC (Nat.cast_nonneg _)
  · exact le_refl 0

theorem logWeight_nonneg' (w : D.what₂.places.Pl) : 0 ≤ SizeData₂.lwP w := by
  simp only [SizeData₂.lwP, lw]
  exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

theorem sumSz_le (C : ℝ) (hC : 0 ≤ C) (y : D.what₂.places.Pl → ℝ)
    (hy : ∀ w, y w ≤ gC L C (D.what₂.places.resChar w)) (hM : Formalism.MainNotions.CornerGLContinuity.MertensBound D) :
    ∑ w ∈ L.supp, SizeData₂.sz w (y w) ≤ 4 * C * Real.log (L.sc.X'' D.R.n + 1) := by
  classical
  have ha := a_nonneg L
  have hX0 : 0 ≤ L.sc.X'' D.R.n := by
    unfold Scale.X''
    exact div_nonneg ha w''_nonneg
  have s1 : ∑ w ∈ L.supp, SizeData₂.sz w (y w) ≤
      2 * ∑ w ∈ L.supp, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * gC L C (D.what₂.places.resChar w) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun w _ => ?_
    unfold SizeData₂.sz
    have hc : 0 ≤ 2 * SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) :=
      mul_nonneg (mul_nonneg zero_le_two (logWeight_nonneg' w)) (Nat.cast_nonneg _)
    calc 2 * SizeData₂.lwP w * ((D.what₂.places.ramIdx w : ℝ) * y w)
        = (2 * SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ)) * y w := by ring
      _ ≤ (2 * SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ)) * gC L C (D.what₂.places.resChar w) :=
          mul_le_mul_of_nonneg_left (hy w) hc
      _ = 2 * (SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * gC L C (D.what₂.places.resChar w)) := by ring
  have s2 := Formalism.MainNotions.G.TopChoiceBounds.bt_sum_by_prime L.supp (gC L C) (gC_nonneg L hC)
  set P' : Finset ℕ := (Finset.range ⌈L.sc.X'' D.R.n + 1⌉₊).filter Nat.Prime with hP'
  have hf0 : ∀ p : ℕ, 0 ≤ C * (Real.log p / p) := fun p =>
    mul_nonneg hC (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
  have hpt : ∀ p ∈ L.supp.image D.what₂.places.resChar,
      Real.log (p : ℝ) * gC L C p ≤ if p ∈ P' then C * (Real.log p / p) else 0 := by
    intro p hp
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.1 hp
    have hpr := D.what₂.places.resChar_prime w
    unfold gC
    split_ifs with h1 h2 h2
    · apply le_of_eq
      ring
    · exfalso
      apply h2
      rw [hP', Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_ceil.2 (by linarith), hpr⟩
    · rw [mul_zero]; exact hf0 _
    · rw [mul_zero]
  have s3 : ∑ p ∈ L.supp.image D.what₂.places.resChar, Real.log (p : ℝ) * gC L C p ≤ ∑ p ∈ P', C * (Real.log p / p) := by
    refine le_trans (Finset.sum_le_sum hpt) ?_
    rw [Finset.sum_ite_mem]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun p _ _ => hf0 p)
  have s4 : ∑ p ∈ P', C * (Real.log p / p) ≤ C * (2 * Real.log (L.sc.X'' D.R.n + 1)) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hM _ (by linarith)) hC
  linarith

theorem wj_bounds (hN : SizeN L) (hK : SizeK L) (hLa : SizeLa L) (hBot : SizeBot L) (hEta : SizeEta L)
    (j : ℕ) (τ : D.what₂.Tau) :
    0 ≤ wj D j τ ∧ wj D j τ ≤ 4 * Formalism.MainNotions.DIV.Proofs.szPol L ^ 5 * L.sc.b := by
  unfold wj
  split_ifs with h
  · exact e_bounds hN hK hLa hBot hEta τ ⟨j - 1, h⟩
  · have hP1 := one_le_szPol L
    have hb1 := one_le_b L
    exact ⟨le_rfl, by positivity⟩

theorem FInert_le (j : ℕ) (W : ℝ) (hW0 : 0 ≤ W) (hW : ∀ τ, 0 ≤ wj D j τ ∧ wj D j τ ≤ W) (hk : 1 ≤ (D.R.k : ℝ))
    (hf : (D.R.f : ℝ) ≤ Formalism.MainNotions.DIV.Proofs.szPol L) (p : ℕ) (hp : p.Prime) :
    FInert D j p ≤ 4 * Formalism.MainNotions.DIV.Proofs.szPol L * ((D.R.k : ℝ) - 1) * W / p := by
  classical
  set Pz := Formalism.MainNotions.DIV.Proofs.szPol L with hPz
  have hP1 : 1 ≤ Pz := one_le_szPol L
  have hk0 : 0 ≤ (D.R.k : ℝ) - 1 := by linarith
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hq : (p : ℝ) ≤ (p : ℝ) ^ 2 - 1 := by nlinarith
  have hq0 : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by linarith
  have hA : 0 ≤ ((D.R.k : ℝ) - 1) * W := mul_nonneg hk0 hW0
  unfold FInert
  split_ifs with hc
  · have hterm : ∀ τ : D.what₂.Tau, ((D.R.k : ℝ) - 1) * wj D j τ / ((p : ℝ) ^ 2 - 1) ≤ ((D.R.k : ℝ) - 1) * W / p := by
      intro τ
      rw [div_le_div_iff₀ hq0 hp0]
      have h1 : ((D.R.k : ℝ) - 1) * wj D j τ ≤ ((D.R.k : ℝ) - 1) * W := mul_le_mul_of_nonneg_left (hW τ).2 hk0
      have h2 : 0 ≤ ((D.R.k : ℝ) - 1) * wj D j τ := mul_nonneg hk0 (hW τ).1
      nlinarith
    refine le_trans (Finset.sum_le_sum fun τ _ => hterm τ) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc1 : ((Finset.univ : Finset D.what₂.Tau).card : ℝ) ≤ Pz := card_Tau (L := L)
    have hB : 0 ≤ ((D.R.k : ℝ) - 1) * W / p := div_nonneg hA hp0.le
    have e : 4 * Pz * ((D.R.k : ℝ) - 1) * W / p = 4 * Pz * (((D.R.k : ℝ) - 1) * W / p) := by ring
    rw [e]
    nlinarith
  · have hn0 : (0 : ℝ) < nP D p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne _)
    have hg : (p : ℝ) / ((p : ℝ) ^ 2 - 1) ≤ 2 / p := by
      rw [div_le_div_iff₀ hq0 hp0]
      nlinarith
    have hg0 : 0 ≤ (p : ℝ) / ((p : ℝ) ^ 2 - 1) := div_nonneg hp0.le hq0.le
    have horb : ∀ z : Bool × HH D, FOrb D j p z ≤ 2 / p * ((nP D p : ℝ) * (((D.R.k : ℝ) - 1) * W)) := by
      intro z
      unfold FOrb
      refine le_trans (Formalism.MainNotions.WeilJacquetShalikaLaw.Proof.sz_lpF_le _ _ _) ?_
      have hs : ∑ s : ZMod (nP D p), ((D.R.k : ℝ) - 1) * wPl D j (posPl D p z s.val) ≤
          (nP D p : ℝ) * (((D.R.k : ℝ) - 1) * W) := by
        refine le_trans (Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hW _).2 hk0) ?_
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      have hs0 : 0 ≤ (nP D p : ℝ) * (((D.R.k : ℝ) - 1) * W) := mul_nonneg hn0.le hA
      calc (p : ℝ) / ((p : ℝ) ^ 2 - 1) * ∑ s : ZMod (nP D p), ((D.R.k : ℝ) - 1) * wPl D j (posPl D p z s.val)
          ≤ (p : ℝ) / ((p : ℝ) ^ 2 - 1) * ((nP D p : ℝ) * (((D.R.k : ℝ) - 1) * W)) :=
            mul_le_mul_of_nonneg_left hs hg0
        _ ≤ 2 / p * ((nP D p : ℝ) * (((D.R.k : ℝ) - 1) * W)) := mul_le_mul_of_nonneg_right hg hs0
    have hsum : ∑ z : Bool × HH D, FOrb D j p z ≤
        (Fintype.card (Bool × HH D) : ℝ) * (2 / p * ((nP D p : ℝ) * (((D.R.k : ℝ) - 1) * W))) := by
      refine le_trans (Finset.sum_le_sum fun z _ => horb z) ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card (Bool × HH D) : ℝ) ≤ Pz := by
      rw [Fintype.card_prod, Fintype.card_bool, Formalism.HC.Frame.card_A]
      have hfe : (D.R.f : ℝ) = 2 * D.R.n := Formalism.MainNotions.DIV.Proofs.HHParts.f_eq
      have hn : (D.R.n : ℝ) = (D.R.ord : ℝ) := rfl
      push_cast
      rw [← hn]
      linarith
    rw [div_le_iff₀ hn0]
    have hB : 0 ≤ 2 / p * ((nP D p : ℝ) * (((D.R.k : ℝ) - 1) * W)) :=
      mul_nonneg (div_nonneg zero_le_two hp0.le) (mul_nonneg hn0.le hA)
    have h1 : (Fintype.card (Bool × HH D) : ℝ) * (2 / p * ((nP D p : ℝ) * (((D.R.k : ℝ) - 1) * W))) ≤
        Pz * (2 / p * ((nP D p : ℝ) * (((D.R.k : ℝ) - 1) * W))) := mul_le_mul_of_nonneg_right hcard hB
    have e : 4 * Pz * ((D.R.k : ℝ) - 1) * W / p * (nP D p : ℝ) =
        2 * (Pz * (2 / p * ((nP D p : ℝ) * (((D.R.k : ℝ) - 1) * W)))) := by
      field_simp
      ring
    rw [e]
    have hPB : 0 ≤ Pz * (2 / p * ((nP D p : ℝ) * (((D.R.k : ℝ) - 1) * W))) := mul_nonneg (by linarith) hB
    linarith

theorem F_le (hFD : L.FDef) (hS : SizesAt L) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (w : D.what₂.places.Pl) :
    L.F j w ≤ gC L (16 * Formalism.MainNotions.DIV.Proofs.szPol L ^ 7 * L.sc.b) (D.what₂.places.resChar w) := by
  classical
  obtain ⟨hN, -, hK, -, -, -, -, -, hLa, -, hBot, -, -, hEta, -⟩ := hS
  set Pz := Formalism.MainNotions.DIV.Proofs.szPol L with hPz
  have hP1 : 1 ≤ Pz := one_le_szPol L
  have hb1 := one_le_b L
  have hC : 0 ≤ 16 * Pz ^ 7 * L.sc.b := by positivity
  have hW := wj_bounds hN hK hLa hBot hEta j
  have hW0 : 0 ≤ 4 * Pz ^ 5 * L.sc.b := by positivity
  have hk : 1 ≤ (D.R.k : ℝ) := k_one hK
  have hkP : (D.R.k : ℝ) ≤ Pz := k_le L
  have hp := D.what₂.places.resChar_prime w
  have hp0 : (0 : ℝ) < D.what₂.places.resChar w := by exact_mod_cast hp.pos
  have hg0 := gC_nonneg L hC (D.what₂.places.resChar w)
  rw [hFD j hj w]
  unfold Fval FvalP
  split_ifs with h1 h2 h3
  ·
    unfold FTypeG
    have hd : (0 : ℝ) ≤ (fockDeg D j : ℝ) := by
      have : (0 : ℤ) ≤ fockDeg D j := by
        unfold fockDeg
        exact Finset.sum_nonneg fun τ _ => add_nonneg (Finset.sum_nonneg fun a _ => abs_nonneg _)
          (Finset.sum_nonneg fun a _ => abs_nonneg _)
      exact_mod_cast this
    have : -((fockDeg D j : ℝ)) / 2 ≤ 0 := by linarith
    linarith
  ·
    unfold FRamD
    have hs : 0 ≤ ∑ t : HH D, min (wPl D j (false, t)) (wPl D j (true, t)) :=
      Finset.sum_nonneg fun t _ => le_min (hW _).1 (hW _).1
    have : -(((D.R.k : ℝ) - 1) / 2) * ∑ t : HH D, min (wPl D j (false, t)) (wPl D j (true, t)) ≤ 0 := by
      have hk2 : 0 ≤ ((D.R.k : ℝ) - 1) / 2 := by linarith
      nlinarith
    linarith
  ·
    have hI := FInert_le j (4 * Pz ^ 5 * L.sc.b) hW0 hW hk (f_le L) _ hp
    unfold gC
    rw [if_pos h3.2]
    refine le_trans hI ?_
    rw [div_le_div_iff_of_pos_right hp0]
    have hk0 : 0 ≤ (D.R.k : ℝ) - 1 := by linarith
    have e1 : ((D.R.k : ℝ) - 1) ≤ Pz := by linarith
    have e2 : 4 * Pz * ((D.R.k : ℝ) - 1) ≤ 4 * Pz * Pz := by nlinarith
    have e3 : 4 * Pz * ((D.R.k : ℝ) - 1) * (4 * Pz ^ 5 * L.sc.b) ≤ 4 * Pz * Pz * (4 * Pz ^ 5 * L.sc.b) :=
      mul_le_mul_of_nonneg_right e2 hW0
    have e4 : 4 * Pz * Pz * (4 * Pz ^ 5 * L.sc.b) = 16 * Pz ^ 7 * L.sc.b := by ring
    linarith
  · exact hg0

theorem fo_le_pol (hFD : L.FDef) (hS : SizesAt L) (hM : Formalism.MainNotions.CornerGLContinuity.MertensBound D) :
    L.Fo ≤ 256 * Formalism.MainNotions.DIV.Proofs.szPol L ^ 9 * L.sc.b := by
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := lt_trans zero_lt_one hx1
  have hb : 0 < L.sc.b := by
    simp only [Scale.b]
    exact Real.exp_pos _
  have hL0 : 0 ≤ L.sc.L := by
    simp only [Scale.L]
    exact Real.rpow_nonneg hx0.le _
  have hf : (0 : ℝ) ≤ (D.R.f : ℝ) := by positivity
  have hk0 : (0 : ℝ) ≤ (D.R.k : ℝ) := by positivity
  have hm0 : (0 : ℝ) ≤ (D.R.m : ℝ) := by positivity
  have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := by positivity
  have hNm : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) := by positivity
  have hmP : (D.R.m : ℝ) ≤ Formalism.MainNotions.DIV.Proofs.szPol L := by
    unfold Formalism.MainNotions.DIV.Proofs.szPol; linarith
  have hQ1 : 1 ≤ Formalism.MainNotions.DIV.Proofs.szPol L := by
    unfold Formalism.MainNotions.DIV.Proofs.szPol; linarith
  have hQ0 : 0 ≤ Formalism.MainNotions.DIV.Proofs.szPol L := by linarith
  have hC0 : 0 ≤ 16 * Formalism.MainNotions.DIV.Proofs.szPol L ^ 7 * L.sc.b :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hQ0 7)) hb.le
  have hj : ∀ j ∈ SizeData₂.lifts D, ∑ w ∈ L.supp, SizeData₂.sz w (L.F j w) ≤
      4 * (16 * Formalism.MainNotions.DIV.Proofs.szPol L ^ 7 * L.sc.b) * Real.log (L.sc.X'' D.R.n + 1) :=
    fun j hj => sumSz_le _ hC0 (fun w => L.F j w) (fun w => F_le hFD hS j hj w) hM
  have hsum : L.Fo ≤ ∑ j ∈ SizeData₂.lifts D,
      4 * (16 * Formalism.MainNotions.DIV.Proofs.szPol L ^ 7 * L.sc.b) * Real.log (L.sc.X'' D.R.n + 1) := by
    unfold SizeData₂.Fo
    exact Finset.sum_le_sum hj
  rw [Finset.sum_const, nsmul_eq_mul, Formalism.MainNotions.DIV.HookProducts.Row4.card_lifts_eq] at hsum
  have hlog := Formalism.MainNotions.DIV.HookProducts.Row4.logX_le hS.1 hS.2.2.1
  have hC4 : 0 ≤ 4 * (16 * Formalism.MainNotions.DIV.Proofs.szPol L ^ 7 * L.sc.b) := by linarith
  have s1 : (D.R.m : ℝ) * (4 * (16 * Formalism.MainNotions.DIV.Proofs.szPol L ^ 7 * L.sc.b) *
      Real.log (L.sc.X'' D.R.n + 1)) ≤
      (D.R.m : ℝ) * (4 * (16 * Formalism.MainNotions.DIV.Proofs.szPol L ^ 7 * L.sc.b) *
      (4 * Formalism.MainNotions.DIV.Proofs.szPol L)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog hC4) hm0
  have s2 : (D.R.m : ℝ) * (4 * (16 * Formalism.MainNotions.DIV.Proofs.szPol L ^ 7 * L.sc.b) *
      (4 * Formalism.MainNotions.DIV.Proofs.szPol L)) ≤
      Formalism.MainNotions.DIV.Proofs.szPol L * (4 * (16 * Formalism.MainNotions.DIV.Proofs.szPol L ^ 7 * L.sc.b) *
      (4 * Formalism.MainNotions.DIV.Proofs.szPol L)) :=
    mul_le_mul_of_nonneg_right hmP (mul_nonneg hC4 (by linarith))
  linarith [hsum, s1, s2]

theorem fo_pow {eps : ℝ} (Fm : FamP eps) :
    ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x,
      (Fm.L x i).Fo ≤ x ^ (9 * (max Fm.Ct 5 + 3) + 1) * (Fm.L x i).sc.b := by
  refine ⟨256, fun x hx hx1 i => ?_⟩
  have h := fo_le_pol (Fm.ex x hx1 i).fdef (Fm.sizes x hx1 i) (Formalism.MainNotions.G.Joints.Lit.mertens_bound _)
  have hX : (Fm.L x i).sc.x = x := Fm.L_x x i hx1
  have hCt : (Fm.L x i).Ct = Fm.Ct := Fm.Ct_eq x i
  have hb := Formalism.MainNotions.DIV.Proofs.bPol_le (Fm.sizes x hx1 i) 256 9 (by rw [hX]; norm_num; linarith)
  rw [hX, hCt] at hb
  have e : ((9 : ℕ) : ℝ) * (max Fm.Ct 5 + 3) + 1 = 9 * (max Fm.Ct 5 + 3) + 1 := by norm_num
  rw [e] at hb
  exact h.trans hb

end Formalism.MainNotions.DIV.HookProducts.HookProductWeightBounds

end
