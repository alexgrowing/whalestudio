import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleRanksRankComplement

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open Formalism.BasicNotions

def scBig (B : ℕ) : Scale where
  x := ((B + 2 : ℕ) : ℝ) ^ (500 : ℝ)
  eps := 1 / 100
  one_lt_alt := by
    apply Real.one_lt_rpow _ (by norm_num)
    have : (2 : ℝ) ≤ ((B + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ B + 2)
    linarith
  eps_pos := by norm_num
  eps_lt := by norm_num
  J := 1
  one_le_J := le_rfl

theorem scBig_floor (B : ℕ) : ⌊(scBig B).x ^ ((scBig B).ez / 5)⌋₊ = B + 2 := by
  have h0 : (0 : ℝ) ≤ ((B + 2 : ℕ) : ℝ) := by positivity
  have ee : (scBig B).ez = (scBig B).eps := div_one _
  rw [ee]
  simp only [scBig]
  rw [← Real.rpow_mul h0]
  have e : (500 : ℝ) * (1 / 100 / 5) = 1 := by norm_num
  rw [e, Real.rpow_one, Nat.floor_natCast]

theorem sizeData_sc_not_surjective : ∀ D : D7, ¬ ∀ sc : Scale, ∃ L : SizeData₂ D, L.sc = sc := by
  intro D h
  obtain ⟨L, hL⟩ := h (scBig D.host.splitBound)
  have h1 := L.split_tie
  rw [hL, scBig_floor] at h1
  omega

theorem scale_a_nonneg (sc : Scale) : 0 ≤ sc.a := by
  unfold Scale.a Scale.b
  have := sc.one_lt_alt
  positivity

theorem scale_L_pos (sc : Scale) : 0 < sc.L := by
  unfold Scale.L
  exact Real.rpow_pos_of_pos (by linarith [sc.one_lt_alt]) _

def toySizeData (D : D7) (sc : Scale)
    (hTT : D.host.TT = ∅)
    (hEta : ∀ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.etaJ j w = 0)
    (hTu : ∀ u, sc.b ^ ((D.R.m : ℝ) / 2) ≤ ((D.mem u).A.T : ℝ))
    (hb : ∀ τ j, (((D.hc τ).b j : ℚ) : ℝ) ≤ sc.b ^ 2)
    (hsplit : ⌊sc.x ^ (sc.ez / 5)⌋₊ ≤ D.host.splitBound)
    (ho : (D.R.o : ℝ) ≤ sc.x ^ (sc.eps / 100))
    (hQS : (D.host.QS : ℝ) ≤ 4 * D.R.n * sc.x ^ (sc.eps / 100))
    (j0 : ℕ) (hj0 : Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m) ≤ j0)
    (hLw : 10 * j0 + 20 ≤ D.host.Lw)
    (hT2 : 0 < D.host.T2.card ∧ D.host.T2.card ≤ D.R.n)
    (hmu : ∀ j w, D.what₂.Aj j w = 0)
    (η Cc : ℝ) (hη : 0 < η)
    (hthick : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ,
      (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces →
      sc.b ≤ wj D j τ ∧ wj D j τ ≤ sc.b + η + 1)
    (hthin : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, D.host.IsThin (D.eTau τ : D.R.GG) →
      sc.w'' D.R.n ≤ wj D j τ ∧ wj D j τ ≤ sc.w'' D.R.n + η)
    (hcg : ∀ τ (h0 : 0 < D.R.k - 1), (D.eTau τ : D.R.GG) ∉ D.host.topPlaces →
      (D.R.k : ℝ) * (4 * (D.s.Del : ℝ)) ≤ (((D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) ∧
      (((D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) ≤ Cc * ((D.R.k : ℝ) * (4 * (D.s.Del : ℝ))))
    (hcv : ∀ τ (i : Fin (D.R.k - 1)), 0 ≤ (((D.hc τ).v i : ℚ) : ℝ) ∧
      (((D.hc τ).v i : ℚ) : ℝ) ≤ (D.R.k : ℝ) * (4 * (D.s.Del : ℝ)))
    (hcu : ∀ u τ (i : Fin D.R.k), 1 ≤ i.1 → i.1 + 1 < D.R.k →
      0 ≤ (((D.hcW u τ).u i : ℚ) : ℝ) ∧ (((D.hcW u τ).u i : ℚ) : ℝ) ≤ (D.R.k : ℝ) * (4 * (D.s.Del : ℝ)))
    (hbe : ∀ τ (i j : Fin D.R.m), |(((D.hc τ).b i - (D.hc τ).e j : ℚ) : ℝ)| ≤ η) : SizeData₂ D where
  sc := sc
  aT := fun _ => 0
  aT_win := fun t => ((Finset.eq_empty_iff_forall_notMem.mp hTT) t.1 t.2).elim
  bT := fun _ => 0
  bT_ge := fun t => ((Finset.eq_empty_iff_forall_notMem.mp hTT) t.1 t.2).elim
  top_u := fun _ t _ _ => ((Finset.eq_empty_iff_forall_notMem.mp hTT) t.1 t.2).elim
  top_b := fun _ t _ _ => ((Finset.eq_empty_iff_forall_notMem.mp hTT) t.1 t.2).elim
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
  b_le := hb
  F_conj := fun _ _ => rfl
  F_above := by intros; rfl
  not_inert := fun _ _ _ => ⟨fun _ => rfl, rfl, rfl⟩
  untwisted := fun w _ j _ _ => ⟨hmu j w, rfl⟩
  drop := ∅
  drop_alt := by intros; simp
  j0 := j0
  logFiveDepth_le := hj0
  weightLength_ge_depth := hLw
  logDerivativeAtOne := dlogL D 1
  logDerivative_at_one_eq := rfl
  split_tie := hsplit
  o_tie := ho
  QS_tie := hQS
  NuLat := fun _ => ⊤
  de2 := (D.host.T2.card : ℝ) / (D.R.n : ℝ)
  typeDensity_eq_card_div := rfl
  thickDensity_pos := div_pos (by exact_mod_cast hT2.1) (by exact_mod_cast lt_of_lt_of_le hT2.1 hT2.2)
  thickDensity_le_one := div_le_one_of_le₀ (by exact_mod_cast hT2.2) (by positivity)
  LaG := 0
  Sc := (D.R.k : ℝ) * (4 * (D.s.Del : ℝ))
  etaSz := η
  Cc := Cc
  win_thick := hthick
  win_top := fun _ _ _ _ t _ => ((Finset.eq_empty_iff_forall_notMem.mp hTT) t.1 t.2).elim
  win_thin := hthin
  cloud_gap := hcg
  cloud_v := hcv
  cloud_u := hcu
  be_close := hbe
  Sc_pos := by
    have h1 : (0 : ℝ) < (D.s.Del : ℝ) := by exact_mod_cast D.s.Del_pos
    have h2 : (0 : ℝ) < (D.R.k : ℝ) := by
      have := D.R.m_add_three_le_k
      exact_mod_cast (by omega : 0 < D.R.k)
    positivity
  Sc_eq := rfl
  etaSz_pos := hη
  TTw := fun _ => Finset.univ
  TTw_full := fun _ _ => rfl
  Ct := Real.logb sc.x D.R.t
  t_win := by
    have hx := sc.one_lt_alt
    have ht : (0 : ℝ) < (D.R.t : ℝ) := by
      have := D.R.t_odd.pos
      exact_mod_cast this
    rw [Real.rpow_logb (by linarith) (by linarith) ht]
    exact ⟨by exact_mod_cast D.R.t_odd.pos, le_refl _⟩
  CGam := Real.log (D.mem D.u₀).A.GamP / ((D.R.m : ℝ) ^ 5 * D.R.f * sc.L)
  CGam_pos := by
    have h1 : 0 < Real.log (D.mem D.u₀).A.GamP := Real.log_pos (D.mem D.u₀).A.one_lt_gammaP
    have h2 : (0 : ℝ) < (D.R.m : ℝ) := by
      have := D.R.two_le_m
      exact_mod_cast (by omega : 0 < D.R.m)
    have h3 : (0 : ℝ) < (D.R.f : ℝ) := by
      have : 0 < D.R.f := by unfold Ranks.f Ranks.n; positivity
      exact_mod_cast this
    have h4 := scale_L_pos sc
    exact div_pos h1 (mul_pos (mul_pos (pow_pos h2 5) h3) h4)
  Gam_eq := fun u => by
    have h2 : (0 : ℝ) < (D.R.m : ℝ) := by
      have := D.R.two_le_m
      exact_mod_cast (by omega : 0 < D.R.m)
    have h3 : (0 : ℝ) < (D.R.f : ℝ) := by
      have : 0 < D.R.f := by unfold Ranks.f Ranks.n; positivity
      exact_mod_cast this
    have h4 := scale_L_pos sc
    have hX : ((D.R.m : ℝ) ^ 5 * D.R.f * sc.L) ≠ 0 :=
      ne_of_gt (mul_pos (mul_pos (pow_pos h2 5) h3) h4)
    rw [D.GamP_eq u]
    symm
    calc Real.log (D.mem D.u₀).A.GamP / ((D.R.m : ℝ) ^ 5 * D.R.f * sc.L) * (D.R.m : ℝ) ^ 5 *
          D.R.f * sc.L
        = Real.log (D.mem D.u₀).A.GamP / ((D.R.m : ℝ) ^ 5 * D.R.f * sc.L) *
          ((D.R.m : ℝ) ^ 5 * D.R.f * sc.L) := by ring
      _ = Real.log (D.mem D.u₀).A.GamP := div_mul_cancel₀ _ hX
  wPart := fun _ _ _ _ => 1
  wPart_ge := fun _ _ _ _ => le_rfl
  lenMN := fun _ _ => 0

theorem toySizeData_sc (D : D7) (sc : Scale) (hTT hEta hTu hb hsplit ho hQS j0 hj0 hLw hT2 hmu η Cc hη hthick hthin
    hcg hcv hcu hbe) :
    (toySizeData D sc hTT hEta hTu hb hsplit ho hQS j0 hj0 hLw hT2 hmu η Cc hη hthick hthin hcg hcv hcu hbe).sc = sc :=
  rfl

def sc0 : Scale where
  x := (2 : ℝ) ^ (200 : ℝ)
  eps := 1 / 100
  one_lt_alt := Real.one_lt_rpow (by norm_num) (by norm_num)
  eps_pos := by norm_num
  eps_lt := by norm_num
  J := 1
  one_le_J := le_rfl

theorem exampleScale_ez_eq : sc0.ez = sc0.eps := div_one _

theorem scale_one_le_rpow (sc : Scale) : 1 ≤ sc.x ^ (sc.eps / 100) :=
  Real.one_le_rpow sc.one_lt_alt.le (by have := sc.eps_pos; positivity)

theorem exampleScale_L : sc0.L = 4 := by
  simp only [Scale.L, sc0]
  rw [← Real.rpow_mul (by norm_num)]
  norm_num

theorem exampleScale_b_eq_exp : sc0.b = Real.exp 4 := by
  simp only [Scale.b, exampleScale_L]

theorem exampleScale_split_le_two : ⌊sc0.x ^ (sc0.ez / 5)⌋₊ ≤ 2 := by
  apply Nat.floor_le_of_le
  rw [exampleScale_ez_eq]
  simp only [sc0]
  rw [← Real.rpow_mul (by norm_num)]
  have : (2 : ℝ) ^ ((200 : ℝ) * (1 / 100 / 5)) ≤ 2 ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  simpa using this

theorem exp_four_lt : Real.exp 4 < 55 := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have h0 : 0 < Real.exp 1 := Real.exp_pos 1
  have : Real.exp 1 ^ 4 < 2.7182818286 ^ 4 := by gcongr
  linarith [show (2.7182818286 : ℝ) ^ 4 < 55 by norm_num]

theorem exp_four_gt : 54 < Real.exp 4 := by
  have h := Real.exp_one_gt_d9
  have e : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have : (2.7182818283 : ℝ) ^ 4 < Real.exp 1 ^ 4 := by gcongr
  linarith [show (54 : ℝ) < 2.7182818283 ^ 4 by norm_num]

theorem exampleScale_b_bounds : 54 < sc0.b ∧ sc0.b < 55 := by
  rw [exampleScale_b_eq_exp]; exact ⟨exp_four_gt, exp_four_lt⟩

theorem exampleScale_b_sq_ge : 2900 ≤ sc0.b ^ 2 := by
  have := exampleScale_b_bounds.1
  nlinarith

theorem scale_w''_bounds (sc : Scale) (n : ℕ) (hn : 1 ≤ n) : 0 ≤ sc.w'' n ∧ sc.w'' n ≤ sc.b := by
  have hx : 0 < sc.x := by linarith [sc.one_lt_alt]
  have hb : 0 < sc.b := Real.exp_pos _
  have hX : 1 ≤ sc.X' := Real.one_le_exp (by positivity)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have e : sc.w'' n = sc.b / (n * sc.X') := by
    simp only [Scale.w'', Scale.b', Scale.a]
    field_simp
  rw [e]
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  have h1 : (1 : ℝ) ≤ n * sc.X' := one_le_mul_of_one_le_of_one_le hn' hX
  nlinarith

theorem exampleScale_pow_le_level (m T : ℕ) (hm : m = 2) (hT : 55 ≤ T) : sc0.b ^ ((m : ℝ) / 2) ≤ (T : ℝ) := by
  subst hm
  have h8 : (55 : ℝ) ≤ T := by exact_mod_cast hT
  norm_num
  linarith [exampleScale_b_bounds.2]

theorem exampleRanks_jetIndex_bound : Real.logb 5 ((R0.n : ℝ) * R0.N R0.m / R0.m) ≤ (3 : ℕ) := by
  have e : ((R0.n : ℝ) * R0.N R0.m / R0.m) = 80 := by
    simp [exampleRanks_N_formula]
    norm_num
  rw [e]
  have : Real.logb 5 80 ≤ Real.logb 5 125 :=
    Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by norm_num)
  have e2 : Real.logb 5 125 = 3 := by
    rw [show (125 : ℝ) = 5 ^ (3 : ℕ) by norm_num, Real.logb_pow]
    rw [Real.logb_self_eq_one (by norm_num)]
    norm_num
  push_cast
  linarith

def sizeDataAt0 (D : D7) (hR : D.R = R0) (hTT : D.host.TT = ∅)
    (hEta : ∀ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.etaJ j w = 0)
    (hT : ∀ u, 55 ≤ (D.mem u).A.T) (hsb : 2 ≤ D.host.splitBound) (hQS : D.host.QS ≤ 16) (hLw : 50 ≤ D.host.Lw)
    (hT2 : D.host.T2.card = 1) (hmu : ∀ j w, D.what₂.Aj j w = 0) (hDel : D.s.Del = 1)
    (hv : ∀ τ (i : Fin (D.R.k - 1)), (D.hc τ).v i = 24 - 4 * ((i : ℕ) : ℚ))
    (hu0 : ∀ τ (h : 0 < D.R.k), (D.hc τ).u ⟨0, h⟩ = 113 / 2)
    (hu : ∀ u τ (i : Fin D.R.k), 1 ≤ i.1 → i.1 + 1 < D.R.k →
      (D.hcW u τ).u i = 55 / 2 - 4 * ((i : ℕ) : ℚ))
    (hb : ∀ τ (j : Fin D.R.m), (D.hc τ).b j = 91 + 18 * ((j : ℕ) : ℚ))
    (he : ∀ τ (j : Fin D.R.m), (D.hc τ).e j = 100 + 18 * ((j : ℕ) : ℚ)) : SizeData₂ D :=
  have hk : D.R.k = 8 := by rw [hR]; rfl
  have hm : D.R.m = 2 := by rw [hR]; rfl
  have hn : D.R.n = 4 := by rw [hR]; rfl
  have hSc : (D.R.k : ℝ) * (4 * (D.s.Del : ℝ)) = 32 := by rw [hk, hDel]; norm_num
  have hbb := exampleScale_b_bounds
  have hw := scale_w''_bounds sc0 D.R.n (by omega)
  have hwj : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, 100 ≤ wj D j τ ∧ wj D j τ ≤ 118 := by
    intro j h1 h2 τ
    have h : j - 1 < D.R.m := by omega
    unfold wj
    rw [dif_pos h, he]
    have h3 : ((j - 1 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (by omega : j - 1 ≤ 1)
    have h4 : (0 : ℝ) ≤ ((j - 1 : ℕ) : ℝ) := by positivity
    push_cast
    constructor <;> linarith
  toySizeData D sc0 hTT hEta (fun u => exampleScale_pow_le_level D.R.m _ hm (hT u))
    (fun τ j => by
      rw [hb]
      have h3 : ((j : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (by omega : (j : ℕ) ≤ 1)
      push_cast
      linarith [exampleScale_b_sq_ge])
    (exampleScale_split_le_two.trans hsb)
    (by
      have ho : D.R.o = 1 := by rw [hR]; exact exampleRanks_o
      rw [ho]
      simpa using scale_one_le_rpow sc0)
    (by
      have h1 : (D.host.QS : ℝ) ≤ 16 := by exact_mod_cast hQS
      have h2 := scale_one_le_rpow sc0
      rw [hn]
      push_cast
      linarith)
    3 (by rw [hR]; exact exampleRanks_jetIndex_bound) (by omega) ⟨by omega, by omega⟩ hmu 1000 2 (by norm_num)
    (fun j h1 h2 τ _ => by
      obtain ⟨a1, a2⟩ := hwj j h1 h2 τ
      constructor <;> linarith)
    (fun j h1 h2 τ _ => by
      obtain ⟨a1, a2⟩ := hwj j h1 h2 τ
      constructor <;> linarith)
    (fun τ h0 _ => by
      rw [hSc, hu0, hv]
      norm_num)
    (fun τ i => by
      rw [hSc, hv]
      have h3 : ((i : ℕ) : ℝ) ≤ 6 := by exact_mod_cast (by omega : (i : ℕ) ≤ 6)
      have h4 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := by positivity
      push_cast
      constructor <;> linarith)
    (fun u τ i h1 h2 => by
      rw [hSc, hu u τ i h1 h2]
      have h3 : ((i : ℕ) : ℝ) ≤ 6 := by exact_mod_cast (by omega : (i : ℕ) ≤ 6)
      have h4 : (1 : ℝ) ≤ ((i : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast
      constructor <;> linarith)
    (fun τ i j => by
      rw [hb, he]
      have h3 : ((i : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (by omega : (i : ℕ) ≤ 1)
      have h4 : ((j : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (by omega : (j : ℕ) ≤ 1)
      have h5 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := by positivity
      have h6 : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := by positivity
      push_cast
      rw [abs_le]
      constructor <;> linarith)

theorem sizeDataAt0_sc (D : D7) (hR hTT hEta hT hsb hQS hLw hT2 hmu hDel hv hu0 hu hb he) :
    (sizeDataAt0 D hR hTT hEta hT hsb hQS hLw hT2 hmu hDel hv hu0 hu hb he).sc = sc0 := rfl

end Formalism.BasicNotions.Examples₂
