import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodTopCountLeConstMulLog
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ParametersWindowsOfExplicitParametersStatement

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem bottom_window_le (eps : ℝ) (K : G.Consts) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hK : 1 ≤ K.La) :
    ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R →
      2 * (R.n : ℝ) * s.delta1 * s.x ^ s.eps * G.La K s * s.b' / (R.k : ℝ) ≤ s.b' := by
  obtain ⟨CN, x1, hx1⟩ := GlobalTheory.topCount_and_lambda_bounds eps h0 h1
  refine ⟨max x1 (32 * K.La * CN ^ 2), fun s R he hx hR => ?_⟩
  obtain ⟨-, -, hLa⟩ := hx1 s he (le_trans (le_max_left _ _) hx)
  obtain ⟨hLa1, hLa2⟩ := hLa K hK
  have hx2 : 32 * K.La * CN ^ 2 ≤ s.x := le_trans (le_max_right _ _) hx
  obtain ⟨⟨-, hn⟩, -, ⟨hk, -⟩, -⟩ := hR
  have hx1' : 1 < s.x := s.one_lt_alt
  have hxp : 0 < s.x := by linarith
  have hb : 0 < s.b' := by
    unfold Scale.b' Scale.a Scale.b Scale.X'
    positivity
  have hkp : (0 : ℝ) < R.k := lt_of_lt_of_le (Real.rpow_pos_of_pos hxp _) hk
  have hd0 : 0 < s.delta1 := Real.rpow_pos_of_pos hxp _
  have hd1 : s.delta1 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1'.le (by have := s.eps_pos; linarith)
  have hy : 0 < s.x ^ s.eps := Real.rpow_pos_of_pos hxp _
  have hlog0 : 0 ≤ Real.log s.x := Real.log_nonneg hx1'.le
  have hlog : Real.log s.x ^ 2 ≤ 4 * s.x := by
    have h := Real.log_le_rpow_div hxp.le (show (0 : ℝ) < 1 / 2 by norm_num)
    have h2 : (s.x ^ (1 / 2 : ℝ)) ^ 2 = s.x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hxp.le]; norm_num
    calc Real.log s.x ^ 2 ≤ (s.x ^ (1 / 2 : ℝ) / (1 / 2)) ^ 2 := pow_le_pow_left₀ hlog0 h 2
      _ = 4 * (s.x ^ (1 / 2 : ℝ)) ^ 2 := by ring
      _ = 4 * s.x := by rw [h2]
  have hKC : 0 ≤ K.La * CN ^ 2 := by positivity
  have hLa3 : G.La K s ≤ s.x ^ (2 : ℝ) / 4 * s.x ^ s.eps := by
    refine hLa2.trans ?_
    rw [Real.rpow_two]
    have : K.La * CN ^ 2 * Real.log s.x ^ 2 ≤ s.x / 32 * (4 * s.x) :=
      mul_le_mul (by linarith) hlog (by positivity) (by positivity)
    nlinarith
  have hLa0 : 0 ≤ G.La K s := hy.le.trans hLa1
  have hmain : 2 * (R.n : ℝ) * s.delta1 * s.x ^ s.eps * G.La K s ≤ R.k := by
    calc 2 * (R.n : ℝ) * s.delta1 * s.x ^ s.eps * G.La K s
        ≤ 2 * (2 * s.x ^ (2 + 8 * s.eps)) * 1 * s.x ^ s.eps * (s.x ^ (2 : ℝ) / 4 * s.x ^ s.eps) := by
          gcongr
      _ = s.x ^ (2 + 8 * s.eps) * s.x ^ s.eps * s.x ^ (2 : ℝ) * s.x ^ s.eps := by ring
      _ = s.x ^ (2 + 8 * s.eps + s.eps + 2 + s.eps) := by
          rw [← Real.rpow_add hxp, ← Real.rpow_add hxp, ← Real.rpow_add hxp]
      _ ≤ s.x ^ (9 / 2 + 10 * s.eps) := Real.rpow_le_rpow_of_exponent_le hx1'.le (by linarith)
      _ ≤ R.k := hk
  rw [div_le_iff₀ hkp]
  nlinarith

theorem middle_between {R : Ranks} (p : HCParam R) {S : ℝ}
    (hv : ∀ i : Fin (R.k - 1), 0 ≤ ((p.v i : ℚ) : ℝ) ∧ ((p.v i : ℚ) : ℝ) ≤ S) (i : Fin R.k) (h1 : 1 ≤ i.1)
    (h2 : i.1 + 1 < R.k) : 0 ≤ ((p.u i : ℚ) : ℝ) ∧ ((p.u i : ℚ) : ℝ) ≤ S := by
  obtain ⟨i, hi⟩ := i
  simp only at h1 h2
  have ha := p.u_gt_v ⟨i, by omega⟩
  have hb := p.v_gt_u ⟨i - 1, by omega⟩
  have he : (⟨i - 1 + 1, by omega⟩ : Fin R.k) = ⟨i, hi⟩ := Fin.ext (by simp only; omega)
  simp only [he] at hb
  have ha' : ((p.v ⟨i, by omega⟩ : ℚ) : ℝ) < ((p.u ⟨i, hi⟩ : ℚ) : ℝ) := by exact_mod_cast ha
  have hb' : ((p.u ⟨i, hi⟩ : ℚ) : ℝ) < ((p.v ⟨i - 1, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast hb
  exact ⟨(hv _).1.trans ha'.le, hb'.le.trans (hv _).2⟩

theorem exists_sizeData_explicit : ∀ (eps : ℝ) (C : FC) (cD ch : ℝ), 0 < eps → eps < 1 / 52 → Std C → 0 ≤ cD → 402 ≤ ch → ∃ x0 : ℝ, ∀ (s : Scale) (D : D7) (aT bT : D.host.TT → ℤ), s.eps = eps → x0 ≤ s.x → RankVal s D.R → HostVal s C.P.Cpde D.host → HCVal s cD ch D.host (fun τ => (D.eTau τ : D.R.GG)) D.hc bT → |dlogH D.host| ≤ s.x ^ s.eps → D.s.Del = (Delv s cD : ℚ) → D.host.CT2 = C.CT2 → Fintype.card D.what₂.Word = ⌈3 * Real.exp (C.CGam * (D.R.m : ℝ) ^ 5 * D.R.f * s.L) ^ 2 * s.x ^ C.P.CF⌉₊ → D.div.etaF = 6 * s.x ^ (-C.P.CF) → (∀ u, Real.log (D.mem u).A.GamP = C.CGam * (D.R.m : ℝ) ^ 5 * D.R.f * s.L) → (∀ t, (s.a ≤ (aT t : ℝ) ∧ (aT t : ℝ) ≤ s.a + s.a / ((D.R.k : ℝ) * s.x ^ (Scale.A / 2))) ∧ s.b' ≤ (bT t : ℝ) ∧ (bT t : ℝ) ≤ s.b' + 2 * (D.R.n : ℝ) * s.delta1 * s.x ^ s.eps * G.La C.GK s * s.b' / (D.R.k : ℝ)) → (∀ τ (t : D.host.TT) (h : 0 < D.R.k), (D.eTau τ : D.R.GG) = D.R.tau1 t → (D.hc τ).u ⟨0, h⟩ = (aT t : ℚ) + ((D.R.k : ℚ) - 1) / 2 ∧ (D.hc τ).u ⟨D.R.k - 1, by omega⟩ = -(bT t : ℚ) - ((D.R.k : ℚ) - 1) / 2) → (∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m → D.what₂.Aj j w = 0) → ∃ L : SizeData₂ D, L.sc = s ∧ L.aT = aT ∧ L.bT = bT ∧ Val C cD ch L := by
  intro eps C cD ch h0 h1 hC hcD hch
  obtain ⟨hfix, hCc, -, -, -, -, -, -, -, -, -, -, -, -, hmid, -⟩ := hC
  have hLa : 1 ≤ C.GK.La := hmid _ (by simp [FC.cMid])
  have hGam : 1 ≤ C.CGam := hmid _ (by simp [FC.cMid])
  have hCt : C.Ct = 401 := hfix.2.2.2.2.2.2.2.2.2
  obtain ⟨x1, hx1⟩ := bottom_window_le eps C.GK h0 h1 hLa
  obtain ⟨x2, hx2⟩ := GlobalTheory.T.windows_of_explicitParameters eps cD ch C.P.Cpde h0 h1 hcD hch
  refine ⟨max (max x1 x2) ((max C.P.Cpde 1) ^ (100 / eps)), ?_⟩
  intro s D aT bT he hx0 hR hH hHC hdl hDel hCT2 hW heta hG hwin htop hA
  have hx : max x1 x2 ≤ s.x := le_trans (le_max_left _ _) hx0
  have hCo : C.P.Cpde ≤ s.x ^ (s.eps / 100) := by
    have hM : (0 : ℝ) ≤ max C.P.Cpde 1 := le_trans zero_le_one (le_max_right _ _)
    have h3 : (max C.P.Cpde 1) ^ (100 / eps) ≤ s.x := le_trans (le_max_right _ _) hx0
    have h4 := Real.rpow_le_rpow (Real.rpow_nonneg hM _) h3 (show 0 ≤ eps / 100 by positivity)
    rw [← Real.rpow_mul hM, show 100 / eps * (eps / 100) = 1 by field_simp, Real.rpow_one] at h4
    rw [he]
    exact (le_max_left _ _).trans h4
  have hb := hx1 s D.R he (le_trans (le_max_left _ _) hx) hR
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13⟩ :=
    hx2 s D bT he (le_trans (le_max_right _ _) hx) hR hH
      (fun t => ⟨(hwin t).2.1, by linarith [(hwin t).2.2]⟩) hHC
  have hDelR : ((D.s.Del : ℚ) : ℝ) = (Delv s cD : ℝ) := by rw [hDel]; norm_cast
  have hkp : (0 : ℝ) < D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 0 < D.R.k)
  have hmp : (0 : ℝ) < D.R.m := by
    have := D.R.two_le_m
    exact_mod_cast (by omega : 0 < D.R.m)
  have hnp : (0 : ℝ) < D.R.n := by
    unfold Ranks.n
    positivity
  have hxp : 0 < s.x := lt_trans one_pos s.one_lt_alt
  have hh0 : (0 : ℝ) < (h0v s ch : ℝ) := by
    have : 0 < ⌈s.x ^ ch⌉₊ := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hxp _)
    unfold h0v
    exact_mod_cast (by omega : 0 < 2 * ⌈s.x ^ ch⌉₊)
  have hDp : (0 : ℝ) < (Delv s cD : ℝ) := by
    rw [← hDelR]; exact_mod_cast D.s.Del_pos
  let L : SizeData₂ D :=
    { sc := s
      aT := aT
      aT_win := fun t => (hwin t).1
      bT := bT
      bT_ge := fun t => (hwin t).2.1
      top_u := fun τ t h hτ => by
        obtain ⟨e1, e2⟩ := htop τ t h hτ
        rw [e1, e2]
        push_cast
        exact ⟨rfl, rfl⟩
      top_b := w1
      supp := ∅
      gain := fun _ _ => 0
      F := fun _ _ => 0
      E := fun _ _ _ => 0
      tau := fun _ => 0
      io := fun _ => 0
      gain_supp := fun _ _ _ => rfl
      F_supp := fun _ _ _ => rfl
      E_supp := fun _ _ _ _ => rfl
      tau_supp := fun _ _ => rfl
      io_supp := fun _ _ => rfl
      gain_g := fun _ _ _ => rfl
      b_le := w2
      untwisted := fun w h j j1 j2 => ⟨hA w h j j1 j2, rfl⟩
      not_inert := fun _ _ _ => ⟨fun _ => rfl, rfl, rfl⟩
      drop := ∅
      drop_alt := fun _ => Set.notMem_empty _
      F_conj := fun _ _ => rfl
      F_above := fun _ _ _ _ _ => rfl
      j0 := ⌈Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m)⌉₊
      logFiveDepth_le := Nat.le_ceil _
      weightLength_ge_depth := w11
      logDerivativeAtOne := dlogL D 1
      logDerivative_at_one_eq := rfl
      split_tie := hH.split_tie
      o_tie := hH.o_le.trans hCo
      QS_tie := by
        have h3 := hH.QS_le
        have h4 := mul_le_mul_of_nonneg_right hCo hnp.le
        have h5 : 0 ≤ s.x ^ (s.eps / 100) * D.R.n := by positivity
        show (D.host.QS : ℝ) ≤ 4 * D.R.n * s.x ^ (s.eps / 100)
        nlinarith
      NuLat := fun _ => ⊥
      de2 := (D.host.T2.card : ℝ) / D.R.n
      thickDensity_pos := div_pos (by exact_mod_cast w12) hnp
      thickDensity_le_one := (div_le_one hnp).mpr (by exact_mod_cast w13)
      typeDensity_eq_card_div := rfl
      LaG := G.La C.GK s
      Sc := (D.R.k : ℝ) * (4 * (Delv s cD : ℝ))
      etaSz := (D.R.m : ℝ) * (h0v s ch : ℝ)
      Sc_pos := by positivity
      Sc_eq := by rw [hDelR]
      Cc := C.Cc
      win_thick := w3
      win_top := w4
      win_thin := w5
      cloud_gap := by rw [hCc]; exact w6
      cloud_v := w7
      cloud_u := fun u τ i i1 i2 =>
        middle_between (D.hcW u τ) (by rw [D.hcW_v]; exact w7 τ) i i1 i2
      be_close := w8
      etaSz_pos := by positivity
      TTw := fun _ => Finset.univ
      TTw_full := fun _ _ => rfl
      Ct := C.Ct
      t_win := ⟨w9, by rw [hCt]; exact w10⟩
      CGam := C.CGam
      CGam_pos := by linarith
      Gam_eq := hG
      wPart := fun _ _ _ _ => 1
      wPart_ge := fun _ _ _ _ => le_rfl
      lenMN := fun _ _ => 0 }
  exact ⟨L, rfl, rfl, rfl,
    { ranks := hR
      host := hH
      hc := hHC
      dlog := hdl
      Del_eq := hDel
      eta_eq := rfl
      La_eq := rfl
      bT_le := fun t => (hwin t).2.2
      logFiveDepth_eq := rfl
      Ct_eq := rfl
      Cc_eq := rfl
      CGam_eq := rfl
      secondConstant_eq := hCT2
      words := hW
      etaF_eq := heta }⟩

end GlobalTheory.EX
