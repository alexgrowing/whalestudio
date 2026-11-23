import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.TwoHundredLeRadius
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FactorizationBoundMonoLattices
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LocalHypothesisOfGlobal

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

structure JFacts (K : Cst) (X : Dat) : Prop where
  j3 : 3 ≤ X.J0 K
  jb : X.J0 K ≤ X.b' / 216
  cj : (X.ccl : ℝ) ≤ X.J0 K
  jn3 : (3 : ℝ) ≤ X.Jn K
  jnle : (X.Jn K : ℝ) ≤ X.J0 K
  uale : (X.ua : ℝ) ≤ X.ar + X.ar / (((X.m : ℝ) + 1) * X.Y)
  ualt : X.ar + X.ar / (((X.m : ℝ) + 1) * X.Y) < X.ua + 1
  uble : (X.ub : ℝ) ≤ X.bu
  blge : X.b' / 2 ≤ X.bl
  bule : X.bu ≤ 3 * X.b' / 2
  lbge : X.bl ≤ X.lb

theorem jFacts_of {K : Cst} (hK : K.Pos) {CH : ℝ} (hCH : K.TM ≤ CH) {X : Dat} (h : X.Hyp K.C₀ CH) (B : Base K CH X) :
    JFacts K X := by
  have H' := hyp_round hK hCH h B
  obtain ⟨hY, -, -, -, -, -, -, -, hb, hbl, hbu, -, hIb2, hYb, hk2, -, -, -, -, -, hccl, -, -, -⟩ := H'
  obtain ⟨l1, -, -⟩ := La_round hK B
  have hT : K.TLP ≤ CH := le_trans (le_max_left _ _) hCH
  have h108 : (108 : ℝ) ≤ CH := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hYbC : CH ≤ X.Yb := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hk5 : (5 : ℝ) ≤ (X.m : ℝ) + 1 := B.hk5
  have hk0 : (0 : ℝ) < (X.m : ℝ) + 1 := by linarith
  have hN2 : (2 : ℝ) ≤ (X.TT.card : ℝ) := B.hN2
  have hLa1 : 1 ≤ LaI K.C₀ X.N₁ X.ar := B.hLa1
  have hLa' : 1 ≤ LaI K.C₀ X.N₁ (X.a : ℝ) := le_trans hLa1 l1
  have h200 := two_hundred_le_radius B
  have hJ : X.J0 K = LaI K.C₀ X.N₁ (X.a : ℝ) * X.b' / ((X.m : ℝ) + 1) := rfl
  have hbk : 24 * ((X.m : ℝ) + 1) ≤ X.b' := by
    have h1 := B.hsz X.k 8 (by linarith [B.hk5]) (k_le_G B) (by norm_num) (by
      have h8 : 8 ≤ X.cStar := by
        have := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        omega
      have h8' : (8 : ℝ) ≤ X.cStar := by exact_mod_cast h8
      have h1 : (0 : ℝ) ≤ (X.N : ℝ) * X.ccl := by positivity
      have h2 : (0 : ℝ) ≤ (X.n' : ℝ) * X.ccl := by positivity
      linarith)
    have h2 : 108 * (X.k * 8) ≤ CH * (X.k * 8) := mul_le_mul_of_nonneg_right h108 (by linarith [B.hk5])
    have h3 : X.k = (X.m : ℝ) + 1 := rfl
    rw [h3] at h1 h2
    linarith
  have j3 : 3 ≤ X.J0 K := by
    rw [hJ, le_div_iff₀ hk0]
    have : 1 * X.b' ≤ LaI K.C₀ X.N₁ (X.a : ℝ) * X.b' := mul_le_mul_of_nonneg_right hLa' hb.le
    linarith
  have jb : X.J0 K ≤ X.b' / 216 := by
    rw [hJ, div_le_div_iff₀ hk0 (by norm_num)]
    have h1 : 216 * LaI K.C₀ X.N₁ (X.a : ℝ) ≤ (X.m : ℝ) + 1 := by
      have e1 : (108 : ℝ) * 2 ≤ X.Yb * X.TT.card := mul_le_mul (by linarith) hN2 (by norm_num) (by linarith)
      have e2 : 108 * 2 * LaI K.C₀ X.N₁ (X.a : ℝ) ≤ X.Yb * X.TT.card * LaI K.C₀ X.N₁ (X.a : ℝ) :=
        mul_le_mul_of_nonneg_right e1 (by linarith)
      linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hb.le
    linarith
  have hx0 : 0 ≤ X.ar + X.ar / (((X.m : ℝ) + 1) * X.Y) := by
    have : 0 ≤ X.ar := by linarith
    positivity
  refine ⟨j3, jb, hccl, ?_, Nat.floor_le (by linarith), Nat.floor_le hx0, Nat.lt_floor_add_one _,
    Nat.floor_le (by linarith), by linarith, by linarith, Nat.le_ceil _⟩
  have : 3 ≤ X.Jn K := Nat.le_floor (by exact_mod_cast j3)
  exact_mod_cast this

theorem cb_of {K : Cst} {CH : ℝ} {X : Dat} (B : Base K CH X) : CBoundI 4 X.p X.m X.TT X.a X.ccl X.cStar X.c4 := by
  obtain ⟨-, -, h3, -⟩ := logs_of B
  unfold CBoundI Dat.c4 Dat.N
  push_cast
  have h1 : (0 : ℝ) ≤ (X.TT.card : ℝ) * ((X.m : ℝ) + 1) * Real.logb X.p X.a := by positivity
  have h2 : (0 : ℝ) ≤ (X.TT.card : ℝ) * X.ccl := by positivity
  have h4 : (0 : ℝ) ≤ (X.n' : ℝ) * X.ccl := by positivity
  have h5 : (0 : ℝ) ≤ (X.cStar : ℝ) := by positivity
  linarith

theorem D0nn_of {K : Cst} (hK : K.Pos) {CH : ℝ} {X : Dat} (B : Base K CH X) : 0 ≤ X.D0 K := by
  obtain ⟨h1, -, h3, -⟩ := logs_of B
  rw [D0_eq_numSeg_mul_add]
  have hCA : 0 < K.CA := hK.2.2.1
  have hk : 0 ≤ X.k := by linarith [B.hk5]
  have hlg : 0 ≤ lgA X.p X.a X.m := by linarith
  positivity

theorem small_depth_le_large_depth (K : Cst) (X : Dat) : X.D0 K ≤ X.D1 K := by
  unfold Dat.D1
  have : (0 : ℝ) ≤ 4 * (X.N : ℝ) * X.u0c := by positivity
  linarith

theorem window_lower_bound_of_base {K : Cst} {CH : ℝ} {X : Dat} (B : Base K CH X) (J : JFacts K X) :
    (X.a : ℝ) + X.a / (((X.m : ℝ) + 1) * X.Y) ≤ ((X.ua + X.Jn K + X.ccl : ℕ) : ℝ) := by
  have hk5 : (5 : ℝ) ≤ (X.m : ℝ) + 1 := B.hk5
  have hkY : 1 ≤ ((X.m : ℝ) + 1) * X.Y := one_le_mul_of_one_le_of_one_le (by linarith) B.hY
  have hkY0 : 0 < ((X.m : ℝ) + 1) * X.Y := by linarith
  have h1 : (X.a : ℝ) / (((X.m : ℝ) + 1) * X.Y) ≤ X.ar / (((X.m : ℝ) + 1) * X.Y) + 1 := by
    have e1 : (X.a : ℝ) / (((X.m : ℝ) + 1) * X.Y) ≤ (X.ar + 1) / (((X.m : ℝ) + 1) * X.Y) :=
      div_le_div_of_nonneg_right B.haa1.le hkY0.le
    have e2 : 1 / (((X.m : ℝ) + 1) * X.Y) ≤ 1 := (div_le_one hkY0).2 hkY
    rw [add_div] at e1
    linarith
  push_cast
  have := J.ualt
  have := J.jn3
  have := B.haa1
  have : (0 : ℝ) ≤ X.ccl := by positivity
  linarith

theorem winA_of {K : Cst} {CH : ℝ} {X : Dat} (B : Base K CH X) (J : JFacts K X) :
    ((X.ua + X.Jn K + X.ccl : ℕ) : ℝ) ≤ X.a + X.a / (((X.m : ℝ) + 1) * X.Y) + 2 * X.J0 K := by
  have hk5 : (5 : ℝ) ≤ (X.m : ℝ) + 1 := B.hk5
  have hkY0 : 0 < ((X.m : ℝ) + 1) * X.Y := mul_pos (by linarith) (by linarith [B.hY])
  have e1 : X.ar / (((X.m : ℝ) + 1) * X.Y) ≤ (X.a : ℝ) / (((X.m : ℝ) + 1) * X.Y) :=
    div_le_div_of_nonneg_right B.haa hkY0.le
  push_cast
  linarith [J.uale, J.jnle, J.cj, B.haa]

theorem winB_of {K : Cst} {X : Dat} (J : JFacts K X) :
    ((X.ub + X.Jn K + X.ccl : ℕ) : ℝ) ≤ X.bu + 2 * X.J0 K := by
  push_cast
  linarith [J.uble, J.jnle, J.cj]

theorem jA_of {K : Cst} {CH : ℝ} {X : Dat} (B : Base K CH X) (J : JFacts K X) : X.Jn K ≤ X.a := by
  have h : (X.Jn K : ℝ) ≤ X.a := by linarith [J.jnle, J.jb, b_le_a B, B.hb8]
  exact_mod_cast h

theorem jB_of {K : Cst} {CH : ℝ} {X : Dat} (B : Base K CH X) (J : JFacts K X) : X.Jn K ≤ X.lb := by
  have h : (X.Jn K : ℝ) ≤ X.lb := by linarith [J.jnle, J.jb, J.blge, J.lbge, B.hb8]
  exact_mod_cast h

theorem degree_sum_le_eight_mul {K : Cst} {CH : ℝ} {X : Dat} (B : Base K CH X) (J : JFacts K X) :
    (X.ua + X.Jn K + X.ccl) + (X.ub + X.Jn K + X.ccl) + 1 ≤ 8 * X.a := by
  have hk5 : (5 : ℝ) ≤ (X.m : ℝ) + 1 := B.hk5
  have hkY : 1 ≤ ((X.m : ℝ) + 1) * X.Y := one_le_mul_of_one_le_of_one_le (by linarith) B.hY
  have h200 := two_hundred_le_radius B
  have e1 : X.ar / (((X.m : ℝ) + 1) * X.Y) ≤ X.ar := div_le_self (by linarith) hkY
  have h : ((X.ua : ℝ) + X.Jn K + X.ccl) + ((X.ub : ℝ) + X.Jn K + X.ccl) + 1 ≤ 8 * (X.a : ℝ) := by
    linarith [J.uale, J.jnle, J.cj, J.jb, J.uble, J.bule, b_le_a B, B.haa, B.hb8]
  exact_mod_cast h

theorem logl_of {K : Cst} (hK : K.Pos) {CH : ℝ} (hCH : K.TM ≤ CH) {X : Dat} (h : X.Hyp K.C₀ CH) (B : Base K CH X) :
    ((X.m : ℝ) + 1) * X.Y ^ 2 * Real.log X.a ≤ X.a / X.b' := by
  have H' := hyp_round hK hCH h B
  have h16 := H'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨l1, -, -⟩ := La_round hK B
  obtain ⟨g1, -⟩ := log_round B
  have hT : K.TLP ≤ CH := le_trans (le_max_left _ _) hCH
  have h108 : (108 : ℝ) ≤ CH := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hYbC : CH ≤ X.Yb := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hk5 : (5 : ℝ) ≤ (X.m : ℝ) + 1 := B.hk5
  have hN2 : (2 : ℝ) ≤ (X.TT.card : ℝ) := B.hN2
  have hLa' : 1 ≤ LaI K.C₀ X.N₁ (X.a : ℝ) := le_trans B.hLa1 l1
  have hl : 0 ≤ Real.log (X.a : ℝ) := by linarith [B.hlog1]
  refine le_trans ?_ h16
  have e1 : (1 : ℝ) ≤ X.Yb / 2 * X.TT.card * LaI K.C₀ X.N₁ (X.a : ℝ) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)) hLa'
  have hP : 0 ≤ ((X.m : ℝ) + 1) * X.Y ^ 2 * Real.log X.a := by positivity
  have e2 := mul_le_mul_of_nonneg_left e1 hP
  calc _ = ((X.m : ℝ) + 1) * X.Y ^ 2 * Real.log X.a * 1 := by ring
    _ ≤ _ := e2
    _ = _ := by ring

theorem multiplicity_bound_nonneg (K : Cst) (hK : K.Pos) (X : Dat) : 0 ≤ m0I K.Cm X.p X.m X.G' X.N₁ X.c4 := by
  unfold m0I m0G4 m1G4
  have : 0 < K.Cm := hK.2.2.2.2.2.1
  positivity

theorem multiplicity_bound_abstract (Cm CH k N1 Q Y N c S b' : ℝ) (hCm : 0 < Cm) (hCH : 2 * Cm + 24 ≤ CH) (hk : 1 ≤ k) (hN1 : 1 ≤ N1)
    (hQ : 1 ≤ Q) (hY : 1 ≤ Y) (hc0 : 0 ≤ c)
    (hsz : CH * (k ^ 2 * N1 * Q ^ 2 * Y) * (c / 2) ≤ b') :
    (Cm * k * N1 * Q * c + 12 * c) * (k * Q * Y) ≤ b' := by
  refine le_trans ?_ hsz
  have hP : 0 ≤ k ^ 2 * N1 * Q ^ 2 * Y * (c / 2) := by positivity
  have e1 := mul_le_mul_of_nonneg_right hCH hP
  have e2 : k * Q * Y * c ≤ k ^ 2 * N1 * Q ^ 2 * Y * c := by
    have a1 : (1 : ℝ) ≤ k * N1 * Q := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hk hN1) hQ
    have a2 : 0 ≤ k * Q * Y * c := by positivity
    have := mul_le_mul_of_nonneg_right a1 a2
    calc k * Q * Y * c = 1 * (k * Q * Y * c) := by ring
      _ ≤ k * N1 * Q * (k * Q * Y * c) := this
      _ = _ := by ring
  calc (Cm * k * N1 * Q * c + 12 * c) * (k * Q * Y) = Cm * (k ^ 2 * N1 * Q ^ 2 * Y * c) + 12 * (k * Q * Y * c) := by
        ring
    _ ≤ Cm * (k ^ 2 * N1 * Q ^ 2 * Y * c) + 12 * (k ^ 2 * N1 * Q ^ 2 * Y * c) := by linarith
    _ = (2 * Cm + 24) * (k ^ 2 * N1 * Q ^ 2 * Y * (c / 2)) := by ring
    _ ≤ CH * (k ^ 2 * N1 * Q ^ 2 * Y * (c / 2)) := e1
    _ = _ := by ring

theorem multiplicity_bound_le_ratio {K : Cst} (hK : K.Pos) {CH : ℝ} (hCH : K.TM ≤ CH) {X : Dat} (B : Base K CH X) :
    m0I K.Cm X.p X.m X.G' X.N₁ X.c4 ≤ X.b' / (((X.m : ℝ) + 1) * (X.p : ℝ) ^ X.G' * X.Y) := by
  have hk5 : (5 : ℝ) ≤ (X.m : ℝ) + 1 := B.hk5
  have hk1 : (1 : ℝ) ≤ X.k := by linarith [B.hk5]
  have hQ := B.hQ
  have hY := B.hY
  have hpos : 0 < ((X.m : ℝ) + 1) * (X.p : ℝ) ^ X.G' * X.Y := by
    have : (0 : ℝ) < (X.p : ℝ) ^ X.G' := by linarith
    have : (0 : ℝ) < X.Y := by linarith
    positivity
  rw [le_div_iff₀ hpos]
  unfold m0I m0G4 m1G4
  have hCm : 2 * K.Cm + 24 ≤ CH := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCH
  have sq_level_le_degree : (X.N₁ : ℝ) ≤ X.k := le_trans (le_self_pow₀ B.hN1 (by norm_num)) B.sq_level_le_degree
  have hw : X.k ^ 2 * X.N₁ * ((X.p : ℝ) ^ X.G') ^ 2 * X.Y ≤ X.k ^ 3 * X.N * ((X.p : ℝ) ^ X.G') ^ 4 * X.Y := by
    have a1 : X.k ^ 2 * X.N₁ ≤ X.k ^ 3 * X.N := by
      have : X.k ^ 2 * X.N₁ ≤ X.k ^ 2 * X.k := mul_le_mul_of_nonneg_left sq_level_le_degree (by positivity)
      have h2 : X.k ^ 3 * 1 ≤ X.k ^ 3 * X.N := mul_le_mul_of_nonneg_left (by linarith [B.hN2]) (by positivity)
      calc X.k ^ 2 * X.N₁ ≤ X.k ^ 2 * X.k := this
        _ = X.k ^ 3 * 1 := by ring
        _ ≤ _ := h2
    have a2 : ((X.p : ℝ) ^ X.G') ^ 2 ≤ ((X.p : ℝ) ^ X.G') ^ 4 := pow_le_pow_right₀ hQ (by norm_num)
    have a3 : X.k ^ 2 * X.N₁ * ((X.p : ℝ) ^ X.G') ^ 2 ≤ X.k ^ 3 * X.N * ((X.p : ℝ) ^ X.G') ^ 4 :=
      mul_le_mul a1 a2 (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right a3 (by linarith)
  have hu : (X.c4 : ℝ) / 2 ≤ (X.cStar : ℝ) + X.N * X.ccl + X.n' * X.ccl := by
    unfold Dat.c4
    push_cast
    have : (0 : ℝ) ≤ X.cStar := by positivity
    linarith
  have hsz := B.hsz _ _ (by positivity) hw (by positivity) hu
  exact multiplicity_bound_abstract K.Cm CH X.k X.N₁ ((X.p : ℝ) ^ X.G') X.Y X.N X.c4 0 X.b' hK.2.2.2.2.2.1 hCm hk1 B.hN1 hQ hY
    (by positivity) hsz

theorem fixed_weight_facts_of_hyp {K : Cst} (hK : K.Pos) {CH : ℝ} (hCH : K.TM ≤ CH) {X : Dat} (h : X.Hyp K.C₀ CH) : FixedWeightNumericalFacts K X := by
  have hT : K.TLP ≤ CH := le_trans (le_max_left _ _) hCH
  have B := base_of K hK CH hT X h
  have J := jFacts_of hK hCH h B
  have hd := dle_of hK hT h B
  have hcs : 8 * (X.Dp + 1) ≤ X.cStar := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h4 := four_depth_lt_conductor_of_bounds hd hcs
  have h1nn := D1nn_of hK B
  have hm : 2 * X.N₁ + 2 ≤ X.m := h.2.2.2.2.2.2.1
  exact ⟨hyp_round hK hCH h B, cb_of B, by linarith [small_depth_le_large_depth K X], D0nn_of hK B, by linarith, by linarith [J.j3],
    winA_of B J, winB_of J, jA_of B J, jB_of B J, degree_sum_le_eight_mul B J, by omega⟩

theorem mean_kappa_facts_of_hyp {K : Cst} (hK : K.Pos) {CH : ℝ} (hCH : K.TM ≤ CH) {X : Dat} (h : X.Hyp K.C₀ CH) : MeanKappaNumericalFacts K X := by
  have hT : K.TLP ≤ CH := le_trans (le_max_left _ _) hCH
  have B := base_of K hK CH hT X h
  have J := jFacts_of hK hCH h B
  exact ⟨hyp_round hK hCH h B, cb_of B, by linarith [J.j3], window_lower_bound_of_base B J, winA_of B J, winB_of J,
    logl_of hK hCH h B, multiplicity_bound_nonneg K hK X, multiplicity_bound_le_ratio hK hCH B⟩

theorem threshold_fixed_weight_facts (K : Cst) (hK : K.Pos) : TransportedAlt K (fun _ => FixedWeightNumericalFacts K) :=
  ⟨K.TM, 1, TM_pos K, one_pos, fun _ hCH _ _ _ h => fixed_weight_facts_of_hyp hK hCH h⟩

theorem threshold_mean_kappa_facts (K : Cst) (hK : K.Pos) : TransportedAlt K (fun _ => MeanKappaNumericalFacts K) :=
  ⟨K.TM, 1, TM_pos K, one_pos, fun _ hCH _ _ _ h => mean_kappa_facts_of_hyp hK hCH h⟩

end Formalism.MainNotions.flipOneThree.Pf

end
