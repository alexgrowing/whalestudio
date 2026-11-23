import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoLowerBoundLargeConductor

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem numSeg_le_card {n' : ℕ} (TT : Finset (Fin n')) : numSeg TT ≤ TT.card := by
  unfold numSeg evenTops
  rw [Finset.length_sort]
  exact Finset.card_filter_le _ _

def Cst.TLP (K : Cst) : ℝ := max (max 108 (8 * K.CA + 93)) (max 1 (1 / K.C₀ ^ 2))

structure Base (K : Cst) (CH : ℝ) (X : Dat) : Prop where
  hY : 1 ≤ X.Y
  hN2 : (2 : ℝ) ≤ X.N
  hns : (numSeg X.TT : ℝ) ≤ X.N
  hN1 : (1 : ℝ) ≤ X.N₁
  hk5 : (5 : ℝ) ≤ X.k
  hp25 : (25 : ℝ) ≤ X.p
  hkp : X.k ≤ X.p
  hQ : (1 : ℝ) ≤ (X.p : ℝ) ^ X.G'
  hb8 : (8 : ℝ) ≤ X.b'
  hpa : (X.p : ℝ) * X.b' < X.ar
  haa : X.ar ≤ X.a
  haa1 : (X.a : ℝ) < X.ar + 1
  hL1 : 1 ≤ Real.logb X.p X.ar
  hlog1 : 1 ≤ Real.log X.ar
  hLa1 : 1 ≤ LaI K.C₀ X.N₁ X.ar
  hNk : (X.N : ℝ) ≤ X.k
  sq_level_le_degree : (X.N₁ : ℝ) ^ 2 ≤ X.k
  hsz : ∀ w u : ℝ, 0 ≤ w → w ≤ X.k ^ 3 * X.N * ((X.p : ℝ) ^ X.G') ^ 4 * X.Y → 0 ≤ u →
    u ≤ (X.cStar : ℝ) + X.N * X.ccl + X.n' * X.ccl → CH * w * u ≤ X.b'

theorem base_of (K : Cst) (hK : K.Pos) (CH : ℝ) (hCH : K.TLP ≤ CH) (X : Dat) (h : X.Hyp K.C₀ CH) : Base K CH X := by
  obtain ⟨hY, hp, hev, hseg2, hgap, hN1, hm, hLa8, hb, hbl, hbu, hIb1, hIb2, hYb, hk2, hab, hde, hpab, hkLa, hband,
    hccl, hD, hcs, hsize⟩ := h
  have hCH1 : (1 : ℝ) ≤ CH := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCH
  have hCHC : 1 / K.C₀ ^ 2 ≤ CH := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCH
  have hC0 : 0 < K.C₀ := hK.1
  have hns : numSeg X.TT ≤ X.TT.card := numSeg_le_card _
  have hN2n : 2 ≤ X.TT.card := le_trans hseg2 hns
  have hN2 : (2 : ℝ) ≤ (X.TT.card : ℝ) := by exact_mod_cast hN2n
  have hN1r : (1 : ℝ) ≤ (X.N₁ : ℝ) := by exact_mod_cast hN1
  have hm4 : 4 ≤ X.m := by omega
  have hk5 : (5 : ℝ) ≤ (X.m : ℝ) + 1 := by
    have : (4 : ℝ) ≤ (X.m : ℝ) := by exact_mod_cast hm4
    linarith
  have hY2 : (1 : ℝ) ≤ X.Y ^ 2 := one_le_pow₀ hY
  have hkk : ((X.m : ℝ) + 1) ^ 2 ≤ X.p := by
    have : ((X.m : ℝ) + 1) ^ 2 * 1 ≤ ((X.m : ℝ) + 1) ^ 2 * X.Y ^ 2 :=
      mul_le_mul_of_nonneg_left hY2 (by positivity)
    linarith
  have hp25 : (25 : ℝ) ≤ X.p := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5) hk5 2
    norm_num at this
    linarith
  have hkp : (X.m : ℝ) + 1 ≤ X.p :=
    le_trans (le_self_pow₀ (by linarith) (by norm_num)) hkk
  have hQ : (1 : ℝ) ≤ (X.p : ℝ) ^ X.G' := one_le_pow₀ (by linarith)
  have hQ4 : (1 : ℝ) ≤ ((X.p : ℝ) ^ X.G') ^ 4 := one_le_pow₀ hQ
  have hk3 : (1 : ℝ) ≤ ((X.m : ℝ) + 1) ^ 3 := one_le_pow₀ (by linarith)
  have hG1 : (1 : ℝ) ≤ ((X.m : ℝ) + 1) ^ 3 * X.TT.card * ((X.p : ℝ) ^ X.G') ^ 4 * X.Y :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hk3 (by linarith)) hQ4) hY
  have hsz : ∀ w u : ℝ, 0 ≤ w → w ≤ ((X.m : ℝ) + 1) ^ 3 * X.TT.card * ((X.p : ℝ) ^ X.G') ^ 4 * X.Y → 0 ≤ u →
      u ≤ (X.cStar : ℝ) + X.TT.card * X.ccl + X.n' * X.ccl → CH * w * u ≤ X.b' := by
    intro w u hw0 hw hu0 hu
    calc CH * w * u ≤ CH * (((X.m : ℝ) + 1) ^ 3 * X.TT.card * ((X.p : ℝ) ^ X.G') ^ 4 * X.Y) *
          ((X.cStar : ℝ) + X.TT.card * X.ccl + X.n' * X.ccl) := by
            have h0 : (0 : ℝ) ≤ CH := by linarith
            gcongr
      _ = CH * ((X.m : ℝ) + 1) ^ 3 * X.TT.card * ((X.p : ℝ) ^ X.G') ^ 4 *
          ((X.cStar : ℝ) + X.TT.card * X.ccl + X.n' * X.ccl) * X.Y := by ring
      _ ≤ X.b' := hsize
  have hcs8 : (8 : ℝ) ≤ X.cStar := by
    have : 8 ≤ X.cStar := by omega
    exact_mod_cast this
  have hb8 : (8 : ℝ) ≤ X.b' := by
    have := hsz 1 8 zero_le_one hG1 (by norm_num) (by
      have h1 : (0 : ℝ) ≤ (X.TT.card : ℝ) * X.ccl := by positivity
      have h2 : (0 : ℝ) ≤ (X.n' : ℝ) * X.ccl := by positivity
      linarith)
    linarith
  have hpa : (X.p : ℝ) * X.b' < X.ar := by
    rwa [lt_div_iff₀ hb] at hpab
  have har200 : (200 : ℝ) ≤ X.ar := by
    have := mul_le_mul hp25 hb8 (by norm_num) (by linarith)
    linarith
  have hpar : (X.p : ℝ) ≤ X.ar := by
    have := le_mul_of_one_le_right (by linarith : (0 : ℝ) ≤ X.p) (by linarith : (1 : ℝ) ≤ X.b')
    linarith
  have haa : X.ar ≤ X.a := Nat.le_ceil _
  have haa1 : (X.a : ℝ) < X.ar + 1 := Nat.ceil_lt_add_one (by linarith)
  have hp1 : (1 : ℝ) < X.p := by linarith
  have hL1 : 1 ≤ Real.logb X.p X.ar := by
    rw [← Real.logb_self_eq_one hp1]
    exact Real.logb_le_logb_of_le hp1 (by linarith) hpar
  have hlog1 : 1 ≤ Real.log X.ar := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hNY : (2 : ℝ) ≤ (X.TT.card : ℝ) * X.Y := by
    have := mul_le_mul hN2 hY (by norm_num) (by linarith)
    linarith
  have hLa1 : 1 ≤ LaI K.C₀ X.N₁ X.ar := by
    have h2 : Real.log 2 ≤ Real.log ((X.TT.card : ℝ) * X.Y) := Real.log_le_log (by norm_num) hNY
    have := Real.log_two_gt_d9
    linarith
  have hLa2 : 1 ≤ LaI K.C₀ X.N₁ X.ar ^ 2 := one_le_pow₀ hLa1
  have hNk : (X.TT.card : ℝ) ≤ (X.m : ℝ) + 1 := by
    have h1 : (X.TT.card : ℝ) * 1 ≤ (X.TT.card : ℝ) * LaI K.C₀ X.N₁ X.ar ^ 2 :=
      mul_le_mul_of_nonneg_left hLa2 (by positivity)
    have h2 : 1 * ((X.TT.card : ℝ) * LaI K.C₀ X.N₁ X.ar ^ 2) ≤ CH * ((X.TT.card : ℝ) * LaI K.C₀ X.N₁ X.ar ^ 2) :=
      mul_le_mul_of_nonneg_right hCH1 (by positivity)
    linarith
  have sq_level_le_degree : (X.N₁ : ℝ) ^ 2 ≤ (X.m : ℝ) + 1 := by
    have e1 : LaI K.C₀ X.N₁ X.ar ^ 2 = K.C₀ ^ 2 * (X.N₁ : ℝ) ^ 4 * Real.log X.ar ^ 2 := by
      unfold LaI; ring
    have hl2 : 1 ≤ Real.log X.ar ^ 2 := one_le_pow₀ hlog1
    have hc : 1 ≤ CH * K.C₀ ^ 2 := by
      have hpos : 0 < K.C₀ ^ 2 := by positivity
      rw [div_le_iff₀ hpos] at hCHC
      exact hCHC
    have h4 : (X.N₁ : ℝ) ^ 2 ≤ (X.N₁ : ℝ) ^ 4 := pow_le_pow_right₀ hN1r (by norm_num)
    have h5 : (X.N₁ : ℝ) ^ 4 ≤ CH * (X.TT.card : ℝ) * LaI K.C₀ X.N₁ X.ar ^ 2 := by
      rw [e1]
      have hn4 : (0 : ℝ) ≤ (X.N₁ : ℝ) ^ 4 := by positivity
      calc (X.N₁ : ℝ) ^ 4 = 1 * 1 * (X.N₁ : ℝ) ^ 4 * 1 := by ring
        _ ≤ (CH * K.C₀ ^ 2) * (X.TT.card : ℝ) * (X.N₁ : ℝ) ^ 4 * Real.log X.ar ^ 2 := by
            have : (1 : ℝ) ≤ (X.TT.card : ℝ) := by linarith
            gcongr
        _ = _ := by ring
    linarith
  exact ⟨hY, hN2, by exact_mod_cast hns, hN1r, hk5, hp25, hkp, hQ, hb8, hpa, haa, haa1, hL1, hlog1, hLa1, hNk, sq_level_le_degree, hsz⟩

end Formalism.MainNotions.flipOneThree.Pf

end
