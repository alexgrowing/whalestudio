import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.NumBase

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem dle_abs (CA CH N ns N1 k Y L lg la u0 k1 Dp : ℝ) (hCA : 0 < CA) (hCH : 8 * CA + 93 ≤ CH) (hN : 2 ≤ N)
    (hns0 : 0 ≤ ns) (hns : ns ≤ N) (hN1 : 1 ≤ N1) (sq_level_le_degree : N1 ^ 2 ≤ k) (hNk : N ≤ k) (hk : 5 ≤ k) (hY : 1 ≤ Y)
    (hL : 1 ≤ L) (hlg0 : 0 ≤ lg) (hlg : lg ≤ 3 * L) (hla0 : 0 ≤ la) (hla : la ≤ 2 * L)
    (hu0 : u0 ≤ (k + 1) * lg + 1) (hk1 : k1 ≤ (k - 1) ^ 2 * lg + 1)
    (hD : CH * N * Y ^ 2 * (N1 ^ 5 + k ^ 3) * L ≤ Dp) :
    2 * ((ns * (CA * Y ^ 2 * N1 ^ 2 * k ^ 2 * lg + 2 * (2 * N * k * la)) + 4 * (2 * N * k * la)) + 4 * N * u0) +
      N * k1 ≤ Dp := by
  have hN0 : 0 ≤ N := by linarith
  have hk0 : 0 ≤ k := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hN10 : 0 ≤ N1 := by linarith
  have hY2 : 1 ≤ Y ^ 2 := one_le_pow₀ hY
  have hNL : 0 ≤ N * L := mul_nonneg hN0 hL0
  have hk2 : k ^ 2 ≤ Y ^ 2 * k ^ 3 := by
    have h1 : (1 : ℝ) ≤ Y ^ 2 * k := one_le_mul_of_one_le_of_one_le hY2 (by linarith)
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ k ^ 2)
    calc k ^ 2 = k ^ 2 * 1 := by ring
      _ ≤ k ^ 2 * (Y ^ 2 * k) := this
      _ = _ := by ring
  have hk1' : k ≤ k ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
  set P := N * Y ^ 2 * k ^ 3 * L with hP
  have hP0 : 0 ≤ P := by positivity
  have hB : N * k ^ 2 * L ≤ P := by
    have := mul_le_mul_of_nonneg_left hk2 hNL
    calc N * k ^ 2 * L = N * L * k ^ 2 := by ring
      _ ≤ N * L * (Y ^ 2 * k ^ 3) := this
      _ = P := by rw [hP]; ring
  have hA : N * k * L ≤ P := by
    have := mul_le_mul_of_nonneg_left hk1' hNL
    calc N * k * L = N * L * k := by ring
      _ ≤ N * L * k ^ 2 := this
      _ = N * k ^ 2 * L := by ring
      _ ≤ P := hB
  have t1 : ns * (CA * Y ^ 2 * N1 ^ 2 * k ^ 2 * lg) ≤ 3 * CA * P := by
    calc ns * (CA * Y ^ 2 * N1 ^ 2 * k ^ 2 * lg) ≤ N * (CA * Y ^ 2 * k * k ^ 2 * (3 * L)) := by gcongr
      _ = 3 * CA * P := by rw [hP]; ring
  have t2 : ns * (2 * (2 * N * k * la)) ≤ 8 * P := by
    calc ns * (2 * (2 * N * k * la)) ≤ N * (2 * (2 * k * k * (2 * L))) := by gcongr
      _ = 8 * (N * k ^ 2 * L) := by ring
      _ ≤ 8 * P := by linarith
  have t3 : 4 * (2 * N * k * la) ≤ 16 * P := by
    calc 4 * (2 * N * k * la) ≤ 4 * (2 * N * k * (2 * L)) := by gcongr
      _ = 16 * (N * k * L) := by ring
      _ ≤ 16 * P := by linarith
  have hkL : 0 ≤ k * L := mul_nonneg hk0 hL0
  have t4 : 4 * N * u0 ≤ 16 * P := by
    have h1 : u0 ≤ 4 * (k * L) := by
      have h2 : (k + 1) * lg ≤ (k + 1) * (3 * L) := by gcongr
      have h3 : 4 * L ≤ k * L := by
        have := mul_le_mul_of_nonneg_right (by linarith : (4 : ℝ) ≤ k) hL0
        linarith
      nlinarith
    calc 4 * N * u0 ≤ 4 * N * (4 * (k * L)) := by gcongr
      _ = 16 * (N * k * L) := by ring
      _ ≤ 16 * P := by linarith
  have t5 : N * k1 ≤ 4 * P := by
    have h1 : k1 ≤ 4 * (k ^ 2 * L) := by
      have h2 : (k - 1) ^ 2 ≤ k ^ 2 := by nlinarith
      have h3 : (k - 1) ^ 2 * lg ≤ k ^ 2 * (3 * L) := by
        have h0 : (0 : ℝ) ≤ (k - 1) ^ 2 := by positivity
        gcongr
      have h4 : 1 ≤ k ^ 2 * L := one_le_mul_of_one_le_of_one_le (by nlinarith) hL
      linarith
    calc N * k1 ≤ N * (4 * (k ^ 2 * L)) := by gcongr
      _ = 4 * (N * k ^ 2 * L) := by ring
      _ ≤ 4 * P := by linarith
  have hfin : (8 * CA + 93) * P ≤ Dp := by
    have h1 : (8 * CA + 93) * P ≤ CH * P := mul_le_mul_of_nonneg_right hCH hP0
    have h2 : CH * P ≤ CH * N * Y ^ 2 * (N1 ^ 5 + k ^ 3) * L := by
      have hCH0 : 0 ≤ CH := by linarith
      have h5 : (0 : ℝ) ≤ N1 ^ 5 := by positivity
      have : k ^ 3 ≤ N1 ^ 5 + k ^ 3 := by linarith
      calc CH * P = CH * N * Y ^ 2 * k ^ 3 * L := by rw [hP]; ring
        _ ≤ CH * N * Y ^ 2 * (N1 ^ 5 + k ^ 3) * L := by gcongr
    linarith
  have hCAP : 0 ≤ CA * P := mul_nonneg hCA.le hP0
  have e : 2 * ((ns * (CA * Y ^ 2 * N1 ^ 2 * k ^ 2 * lg + 2 * (2 * N * k * la)) + 4 * (2 * N * k * la)) +
      4 * N * u0) + N * k1 =
      2 * ((ns * (CA * Y ^ 2 * N1 ^ 2 * k ^ 2 * lg) + ns * (2 * (2 * N * k * la)) + 4 * (2 * N * k * la)) +
      4 * N * u0) + N * k1 := by ring
  rw [e]
  nlinarith

theorem logs_of {K : Cst} {CH : ℝ} {X : Dat} (B : Base K CH X) :
    1 ≤ lgA X.p X.a X.m ∧ lgA X.p X.a X.m ≤ 3 * Real.logb X.p X.ar ∧
      0 ≤ Real.logb X.p X.a ∧ Real.logb X.p X.a ≤ 2 * Real.logb X.p X.ar := by
  have hp1 : (1 : ℝ) < X.p := by linarith [B.hp25]
  have har200 : (200 : ℝ) ≤ X.ar := by
    have := mul_le_mul B.hp25 B.hb8 (by norm_num) (by linarith [B.hp25])
    linarith [B.hpa]
  have hpar : (X.p : ℝ) ≤ X.ar := by
    have := le_mul_of_one_le_right (by linarith : (0 : ℝ) ≤ X.p) (by linarith [B.hb8] : (1 : ℝ) ≤ X.b')
    linarith [B.hpa]
  have ha1 : (1 : ℝ) ≤ X.a := by linarith [B.haa]
  have hm : (X.m : ℝ) ≤ X.ar := by
    have := B.hkp
    unfold Dat.k at this
    linarith
  have hm0 : (0 : ℝ) ≤ X.m := by positivity
  have hsq : X.ar ^ 2 = X.ar * X.ar := by ring
  have h10 : 10 * X.ar ≤ X.ar ^ 2 := by
    rw [hsq]
    exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have e2 : Real.logb X.p (X.ar ^ 2) = 2 * Real.logb X.p X.ar := by
    rw [Real.logb_pow]; norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold lgA
    have : 0 ≤ Real.logb X.p (8 * (X.a : ℝ) + X.m) := Real.logb_nonneg hp1 (by linarith)
    linarith
  · unfold lgA
    have h1 : Real.logb X.p (8 * (X.a : ℝ) + X.m) ≤ Real.logb X.p (X.ar ^ 2) :=
      Real.logb_le_logb_of_le hp1 (by linarith) (by linarith [B.haa1])
    rw [e2] at h1
    linarith [B.hL1]
  · exact Real.logb_nonneg hp1 ha1
  · have h1 : Real.logb X.p (X.a : ℝ) ≤ Real.logb X.p (X.ar ^ 2) :=
      Real.logb_le_logb_of_le hp1 (by linarith) (by linarith [B.haa1])
    rw [e2] at h1
    exact h1

theorem D0_eq_numSeg_mul_add (K : Cst) (X : Dat) :
    X.D0 K = (numSeg X.TT : ℝ) * (K.CA * X.Y ^ 2 * (X.N₁ : ℝ) ^ 2 * X.k ^ 2 * lgA X.p X.a X.m +
      2 * (2 * X.N * X.k * Real.logb X.p X.a)) + 4 * (2 * X.N * X.k * Real.logb X.p X.a) := by
  unfold Dat.D0 totalDegreeBudget DjI depthD kappaZeroExponent kap0I kap0G4 Dat.k Dat.N
  rfl

theorem D1nn_of {K : Cst} (hK : K.Pos) {CH : ℝ} {X : Dat} (B : Base K CH X) : 0 ≤ X.D1 K := by
  obtain ⟨h1, -, h3, -⟩ := logs_of B
  unfold Dat.D1
  rw [D0_eq_numSeg_mul_add]
  have hCA : 0 < K.CA := hK.2.2.1
  have hk : 0 ≤ X.k := by linarith [B.hk5]
  have hY : 0 ≤ X.Y := by linarith [B.hY]
  have hlg : 0 ≤ lgA X.p X.a X.m := by linarith
  positivity

theorem dle_of {K : Cst} (hK : K.Pos) {CH : ℝ} (hCH : K.TLP ≤ CH) {X : Dat} (h : X.Hyp K.C₀ CH) (B : Base K CH X) :
    2 * X.D1 K + X.N * X.kap1c ≤ X.Dp := by
  obtain ⟨h1, h2, h3, h4⟩ := logs_of B
  have hD : CH * X.N * X.Y ^ 2 * ((X.N₁ : ℝ) ^ 5 + X.k ^ 3) * Real.logb X.p X.ar ≤ X.Dp :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlg0 : 0 ≤ lgA X.p X.a X.m := by linarith
  have hk : 0 ≤ X.k := by linarith [B.hk5]
  have hu : (X.u0c : ℝ) ≤ (X.k + 1) * lgA X.p X.a X.m + 1 := by
    unfold Dat.u0c
    have : (0 : ℝ) ≤ ((X.m : ℝ) + 2) * lgA X.p X.a X.m := by positivity
    have h5 := (Nat.ceil_lt_add_one this).le
    have e : X.k + 1 = (X.m : ℝ) + 2 := by unfold Dat.k; ring
    rw [e]
    exact h5
  have hk1 : (X.kap1c : ℝ) ≤ (X.k - 1) ^ 2 * lgA X.p X.a X.m + 1 := by
    unfold Dat.kap1c
    have : (0 : ℝ) ≤ kappaOneExponent X.p X.a X.m := by unfold kappaOneExponent; positivity
    have h5 := (Nat.ceil_lt_add_one this).le
    have e : (X.k - 1) ^ 2 * lgA X.p X.a X.m = kappaOneExponent X.p X.a X.m := by unfold Dat.k kappaOneExponent; ring
    rw [e]
    exact h5
  have := dle_abs K.CA CH X.N (numSeg X.TT) X.N₁ X.k X.Y (Real.logb X.p X.ar) (lgA X.p X.a X.m)
    (Real.logb X.p X.a) X.u0c X.kap1c X.Dp hK.2.2.1
    (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCH) B.hN2 (by positivity) B.hns B.hN1 B.sq_level_le_degree B.hNk
    B.hk5 B.hY B.hL1 hlg0 h2 h3 h4 hu hk1 hD
  unfold Dat.D1
  rw [D0_eq_numSeg_mul_add]
  exact this

theorem four_depth_lt_conductor_of_bounds {K : Cst} {X : Dat} (hd : 2 * X.D1 K + X.N * X.kap1c ≤ X.Dp) (hc : 8 * (X.Dp + 1) ≤ X.cStar) :
    4 * X.D1 K < X.c4 := by
  have h1 : (0 : ℝ) ≤ (X.N : ℝ) * X.kap1c := by positivity
  have h2 : (8 : ℝ) * ((X.Dp : ℝ) + 1) ≤ X.cStar := by exact_mod_cast hc
  have h3 : (X.cStar : ℝ) ≤ X.c4 := by
    unfold Dat.c4
    push_cast
    have : (0 : ℝ) ≤ 2 * (X.N : ℝ) * X.ccl + 2 * (X.n' : ℝ) * X.ccl := by positivity
    linarith
  have h4 : (0 : ℝ) ≤ X.Dp := by positivity
  linarith

theorem k_le_G {K : Cst} {CH : ℝ} {X : Dat} (B : Base K CH X) :
    X.k ≤ X.k ^ 3 * X.N * ((X.p : ℝ) ^ X.G') ^ 4 * X.Y := by
  have hk1 : (1 : ℝ) ≤ X.k := by linarith [B.hk5]
  have h1 : (1 : ℝ) ≤ X.k ^ 2 * X.N * ((X.p : ℝ) ^ X.G') ^ 4 * X.Y :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hk1) (by linarith [B.hN2])) (one_le_pow₀ B.hQ)) B.hY
  have := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ X.k)
  calc X.k = X.k * 1 := by ring
    _ ≤ X.k * (X.k ^ 2 * X.N * ((X.p : ℝ) ^ X.G') ^ 4 * X.Y) := this
    _ = _ := by ring

theorem Nccl_le (X : Dat) : (X.N : ℝ) * X.ccl ≤ (X.cStar : ℝ) + X.N * X.ccl + X.n' * X.ccl := by
  have h1 : (0 : ℝ) ≤ X.cStar := by positivity
  have h2 : (0 : ℝ) ≤ (X.n' : ℝ) * X.ccl := by positivity
  linarith

theorem eps_of {K : Cst} {CH : ℝ} (hCH : K.TLP ≤ CH) {X : Dat} (B : Base K CH X) :
    12 * (X.N : ℝ) * X.k * X.ccl / X.b' ≤ 1 / 9 := by
  have hb : 0 < X.b' := by linarith [B.hb8]
  have h108 : (108 : ℝ) ≤ CH := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCH
  have h := B.hsz X.k ((X.N : ℝ) * X.ccl) (by linarith [B.hk5]) (k_le_G B) (by positivity) (Nccl_le X)
  have h0 : (0 : ℝ) ≤ X.k * ((X.N : ℝ) * X.ccl) := mul_nonneg (by linarith [B.hk5]) (by positivity)
  have h1 : 108 * (X.k * ((X.N : ℝ) * X.ccl)) ≤ CH * (X.k * ((X.N : ℝ) * X.ccl)) :=
    mul_le_mul_of_nonneg_right h108 h0
  rw [div_le_iff₀ hb]
  linarith

theorem ccl_le_b {K : Cst} {CH : ℝ} (hCH : K.TLP ≤ CH) {X : Dat} (B : Base K CH X) : (X.ccl : ℝ) ≤ X.b' := by
  have h108 : (108 : ℝ) ≤ CH := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCH
  have h := B.hsz X.k ((X.N : ℝ) * X.ccl) (by linarith [B.hk5]) (k_le_G B) (by positivity) (Nccl_le X)
  have hc0 : (0 : ℝ) ≤ X.ccl := by positivity
  have h1 : (1 : ℝ) * 1 * (1 * X.ccl) ≤ CH * X.k * ((X.N : ℝ) * X.ccl) := by
    have a1 : (1 : ℝ) ≤ CH := by linarith
    have a2 : (1 : ℝ) ≤ X.k := by linarith [B.hk5]
    have a3 : (1 : ℝ) ≤ X.N := by linarith [B.hN2]
    gcongr
  linarith

theorem b_le_a {K : Cst} {CH : ℝ} {X : Dat} (B : Base K CH X) : X.b' ≤ X.a := by
  have hb : 0 ≤ X.b' := by linarith [B.hb8]
  have := mul_le_mul_of_nonneg_right (by linarith [B.hp25] : (1 : ℝ) ≤ X.p) hb
  linarith [B.hpa, B.haa]

theorem second_moment_of_columns {K : Cst} {CH : ℝ} (hCH : K.TLP ≤ CH) {X : Dat} (B : Base K CH X) : 2 * X.ccl ≤ 8 * X.a := by
  have h : (X.ccl : ℝ) ≤ X.a := le_trans (ccl_le_b hCH B) (b_le_a B)
  have h' : X.ccl ≤ X.a := by exact_mod_cast h
  omega

theorem lowa_of {K : Cst} {CH : ℝ} {X : Dat} (B : Base K CH X) : X.b' / 3 ≤ X.a := by
  have := b_le_a B
  linarith [B.hb8]

theorem lowb_of {C₀ CH : ℝ} {X : Dat} (h : X.Hyp C₀ CH) : X.b' / 3 ≤ X.bl := by
  obtain ⟨-, -, -, -, -, -, -, -, hb, -, hbu, -, hIb2, -⟩ := h
  linarith

end Formalism.MainNotions.flipOneThree.Pf

end
