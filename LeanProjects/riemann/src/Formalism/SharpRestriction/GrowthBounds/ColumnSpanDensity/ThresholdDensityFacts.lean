import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.DensAbs

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames

def Cst.TM2 (K : Cst) : ℝ := max K.TLP 400

theorem div_small (x w Yb c : ℝ) (hw : 0 < w) (hYb : 400 ≤ Yb) (h : x * Yb ≤ c * w) : x / w ≤ c / Yb := by
  rw [div_le_div_iff₀ hw (by linarith)]
  linarith

set_option maxHeartbeats 1600000 in
theorem threshold_density_facts (K : Cst) (hK : K.Pos) : TransportedAlt K (fun _ => DensityNumericalFacts K) := by
  refine ⟨K.TM2, 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), one_pos, fun CH hCH _ _ X h => ?_⟩
  have hTLP : K.TLP ≤ CH := le_trans (le_max_left _ _) hCH
  have h400 : (400 : ℝ) ≤ CH := le_trans (le_max_right _ _) hCH
  have B := base_of K hK CH hTLP X h
  have Wf := winFacts_of K hK CH hTLP X h
  obtain ⟨l1, l2, -⟩ := La_round hK B
  obtain ⟨hY, hp, hev, hseg2, hgap, hN1, hm, hLa8, hb, hbl, hbu, hIb1, hIb2, hYb, hk2, hab, hde, hpab, hkLa, hband,
    hccl, hD, hcs, hsize⟩ := h
  have hYb400 : (400 : ℝ) ≤ X.Yb := le_trans h400 hYb
  have hN2 : (2 : ℝ) ≤ (X.N : ℝ) := B.hN2
  have hN0 : (0 : ℝ) < (X.N : ℝ) := by linarith
  have hk5 : (5 : ℝ) ≤ X.k := B.hk5
  have hk0 : (0 : ℝ) < X.k := by linarith
  have hLa1 : 1 ≤ LaI K.C₀ X.N₁ X.ar := B.hLa1
  have h200 := two_hundred_le_radius B
  have ha200 : (200 : ℝ) ≤ X.a := le_trans h200 B.haa
  obtain ⟨La, hLa⟩ : ∃ La, La = LaI K.C₀ X.N₁ X.ar := ⟨_, rfl⟩
  obtain ⟨La', hLa'⟩ : ∃ La', La' = LaI K.C₀ X.N₁ (X.a : ℝ) := ⟨_, rfl⟩
  rw [← hLa] at hLa1 l1 l2 hccl hkLa hab hLa8
  rw [← hLa'] at l1 l2
  have hwa := Wf.wa_ge
  have hwb := Wf.wb_ge
  rw [← hLa] at hwa hwb
  have hJ0 : X.J0 K = La' * X.b' / X.k := by rw [hLa']; rfl
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = La * X.b' / X.k := ⟨_, rfl⟩
  have hZk : Z * X.k = La * X.b' := by rw [hZ]; exact div_mul_cancel₀ _ hk0.ne'
  have hcclZ : (X.ccl : ℝ) ≤ Z := by rw [hZ]; exact hccl
  have hJ0Z : X.J0 K ≤ 2 * Z := by
    rw [hJ0, hZ]
    have := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right l2 hb.le) hk0.le
    calc La' * X.b' / X.k ≤ 2 * La * X.b' / X.k := this
      _ = _ := by ring
  have hLa'0 : 0 ≤ La' := by linarith
  have hJ00 : 0 ≤ X.J0 K := by rw [hJ0]; positivity

  have hkLa' : CH * (X.N : ℝ) * La ^ 2 ≤ X.k := hkLa
  have hLaLa : La ≤ La ^ 2 := le_self_pow₀ hLa1 (by norm_num)
  have hCHN : 0 ≤ CH * (X.N : ℝ) := by positivity
  have hkbig : CH * (X.N : ℝ) * La ≤ X.k := le_trans (mul_le_mul_of_nonneg_left hLaLa hCHN) hkLa'
  have hk800 : (800 : ℝ) ≤ X.k := by
    have a1 : (400 : ℝ) * 2 * 1 ≤ CH * (X.N : ℝ) * La := by gcongr
    linarith
  have hm5 : 5 ≤ X.m := by
    have : (5 : ℝ) ≤ (X.m : ℝ) := by
      have : X.k = (X.m : ℝ) + 1 := rfl
      linarith
    exact_mod_cast this

  have hZb : CH * (X.N : ℝ) * Z ≤ X.b' := by
    have a1 : CH * (X.N : ℝ) * La * X.b' ≤ X.k * X.b' := mul_le_mul_of_nonneg_right hkbig hb.le
    have a2 : CH * (X.N : ℝ) * Z * X.k ≤ X.b' * X.k := by
      calc CH * (X.N : ℝ) * Z * X.k = CH * (X.N : ℝ) * (Z * X.k) := by ring
        _ = CH * (X.N : ℝ) * La * X.b' := by rw [hZk]; ring
        _ ≤ X.k * X.b' := a1
        _ = _ := by ring
    exact le_of_mul_le_mul_right a2 hk0
  have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
  have hZ800 : 800 * Z ≤ X.b' := by
    have : (400 : ℝ) * 2 * Z ≤ CH * (X.N : ℝ) * Z := by gcongr
    linarith
  have hkb : CH * X.k * 8 ≤ X.b' := B.hsz X.k 8 hk0.le (k_le_G B) (by norm_num) (by
    have h1 : (0 : ℝ) ≤ (X.N : ℝ) * X.ccl := by positivity
    have h2 : (0 : ℝ) ≤ (X.n' : ℝ) * X.ccl := by positivity
    have h3 : (8 : ℝ) ≤ X.cStar := by
      have : 8 ≤ X.cStar := by omega
      exact_mod_cast this
    linarith)
  have hkb' : 3200 * X.k ≤ X.b' := by
    have : (400 : ℝ) * X.k * 8 ≤ CH * X.k * 8 := by gcongr
    linarith
  have hZ1 : 1 ≤ Z := by
    have a1 : 1 * X.k ≤ Z * X.k := by
      rw [hZk]
      have : 1 * X.b' ≤ La * X.b' := mul_le_mul_of_nonneg_right hLa1 hb.le
      linarith
    exact le_of_mul_le_mul_right a1 hk0

  have hYNZ : 800 ≤ X.Yb * (X.N : ℝ) * Z := by
    have : (400 : ℝ) * 2 * 1 ≤ X.Yb * (X.N : ℝ) * Z := by gcongr
    linarith
  have hwb2 : X.Yb * (X.N : ℝ) * Z / 2 ≤ ((X.Wb 0).card : ℝ) := by
    have : X.Yb * (X.N : ℝ) * La * X.b' / X.k = X.Yb * (X.N : ℝ) * Z := by rw [hZ]; ring
    rw [this] at hwb
    linarith
  have hwa2 : X.Yb * (X.N : ℝ) * Z / 2 ≤ ((X.Wa 0).card : ℝ) := by
    have e1 : X.Yb * (X.N : ℝ) * La * X.b' = X.Yb * (X.N : ℝ) * Z * X.k := by
      rw [mul_assoc (X.Yb * (X.N : ℝ)) Z, hZk]; ring
    have e2 : X.Yb * (X.N : ℝ) * Z * 1 ≤ X.Yb * (X.N : ℝ) * Z * X.k :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    rw [e1] at hwa
    linarith
  have hwaR : (0 : ℝ) < ((X.Wa 0).card : ℝ) := by linarith
  have hwbR : (0 : ℝ) < ((X.Wb 0).card : ℝ) := by linarith
  have hwaN : 0 < (X.Wa 0).card := by exact_mod_cast hwaR
  have hwbN : 0 < (X.Wb 0).card := by exact_mod_cast hwbR
  have cA : (X.WaP K).card = (X.Wa 0).card + (X.Jn K + X.ccl) := by
    have := card_first_window X
    simp only [Dat.WaP, Nat.card_Icc]
    omega
  have cB : (X.WbP K).card = (X.Wb 0).card + (X.Jn K + X.ccl) := by
    have := card_second_window X
    simp only [Dat.WbP, Nat.card_Icc]
    omega
  have hJn : (X.Jn K : ℝ) ≤ X.J0 K := Nat.floor_le hJ00
  have he3 : ((X.Jn K + X.ccl : ℕ) : ℝ) ≤ 3 * Z := by
    push_cast
    linarith
  have he0 : (0 : ℝ) ≤ ((X.Jn K + X.ccl : ℕ) : ℝ) := Nat.cast_nonneg _

  have hmk : (X.m : ℝ) ≤ X.k := by
    have : X.k = (X.m : ℝ) + 1 := rfl
    linarith
  have hmJ : (X.m : ℝ) * X.J0 K ≤ 2 * (La * X.b') := by
    have a1 : (X.m : ℝ) * X.J0 K ≤ X.k * X.J0 K := mul_le_mul_of_nonneg_right hmk hJ00
    have a2 : X.k * X.J0 K ≤ X.k * (2 * Z) := mul_le_mul_of_nonneg_left hJ0Z hk0.le
    have a3 : X.k * (2 * Z) = 2 * (La * X.b') := by rw [← hZk]; ring
    linarith
  have hG : X.Yb * (X.N : ℝ) * (La * X.b') ≤ X.a := by
    rw [le_div_iff₀ hb] at hab
    have hnn : 0 ≤ X.Yb * (X.N : ℝ) * (La * X.b') := by positivity
    have h1 : (1 : ℝ) ≤ X.k * X.Y ^ 2 * Real.log X.ar :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hY)) B.hlog1
    have h2 := mul_le_mul_of_nonneg_left h1 hnn
    have h3 : X.Yb * (X.N : ℝ) * (La * X.b') * (X.k * X.Y ^ 2 * Real.log X.ar) =
        ((X.m : ℝ) + 1) * X.Y ^ 2 * X.Yb * X.TT.card * La * Real.log X.ar * X.b' := by
      unfold Dat.k Dat.N; ring
    linarith [B.haa]
  have hmJ0 : 0 ≤ (X.m : ℝ) * X.J0 K := by positivity
  have ha0 : (0 : ℝ) < X.a := by linarith
  have hx1 : (X.N : ℝ) * ((X.m : ℝ) * X.J0 K / X.a) ≤ 0.005 := by
    have a1 : (X.N : ℝ) * ((X.m : ℝ) * X.J0 K) / X.a ≤ 2 / X.Yb := by
      apply div_small _ _ _ _ ha0 hYb400
      have b1 : (X.N : ℝ) * ((X.m : ℝ) * X.J0 K) * X.Yb ≤ (X.N : ℝ) * (2 * (La * X.b')) * X.Yb := by gcongr
      linarith
    have a2 : 2 / X.Yb ≤ 0.005 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    calc (X.N : ℝ) * ((X.m : ℝ) * X.J0 K / X.a) = (X.N : ℝ) * ((X.m : ℝ) * X.J0 K) / X.a := by ring
      _ ≤ 0.005 := le_trans a1 a2
  have hx2 : (X.N : ℝ) * Real.exp (-La' / 3) ≤ 0.36 := by
    have a1 : Real.exp (-La' / 3) ≤ Real.exp (-La / 3) := Real.exp_le_exp.2 (by linarith)
    have a2 := Nexp_le (X.N : ℝ) X.Y La hN2 hY hLa8
    have a3 := mul_le_mul_of_nonneg_left a1 hN0.le
    linarith
  have h6 : 6 / X.Yb ≤ 0.015 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hx3 : (X.N : ℝ) * (((X.Jn K + X.ccl : ℕ) : ℝ) / ((X.Wa 0).card : ℝ)) ≤ 0.015 := by
    have a1 : (X.N : ℝ) * ((X.Jn K + X.ccl : ℕ) : ℝ) / ((X.Wa 0).card : ℝ) ≤ 6 / X.Yb := by
      apply div_small _ _ _ _ hwaR hYb400
      have b1 : (X.N : ℝ) * ((X.Jn K + X.ccl : ℕ) : ℝ) * X.Yb ≤ (X.N : ℝ) * (3 * Z) * X.Yb := by gcongr
      linarith
    calc _ = (X.N : ℝ) * ((X.Jn K + X.ccl : ℕ) : ℝ) / ((X.Wa 0).card : ℝ) := by ring
      _ ≤ 0.015 := le_trans a1 h6
  have hx4 : (X.N : ℝ) * (((X.Jn K + X.ccl : ℕ) : ℝ) / ((X.Wb 0).card : ℝ)) ≤ 0.015 := by
    have a1 : (X.N : ℝ) * ((X.Jn K + X.ccl : ℕ) : ℝ) / ((X.Wb 0).card : ℝ) ≤ 6 / X.Yb := by
      apply div_small _ _ _ _ hwbR hYb400
      have b1 : (X.N : ℝ) * ((X.Jn K + X.ccl : ℕ) : ℝ) * X.Yb ≤ (X.N : ℝ) * (3 * Z) * X.Yb := by gcongr
      linarith
    calc _ = (X.N : ℝ) * ((X.Jn K + X.ccl : ℕ) : ℝ) / ((X.Wb 0).card : ℝ) := by ring
      _ ≤ 0.015 := le_trans a1 h6
  have hx10 : 0 ≤ (X.m : ℝ) * X.J0 K / X.a := by positivity
  have hx11 : (X.m : ℝ) * X.J0 K / X.a ≤ 1 := by
    have := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ (X.N : ℝ)) hx10
    linarith
  have hx20 : 0 ≤ Real.exp (-La' / 3) := (Real.exp_pos _).le
  have hx21 : Real.exp (-La' / 3) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hN1n : 1 ≤ X.N := by
    have : (1 : ℝ) ≤ (X.N : ℝ) := by linarith
    exact_mod_cast this
  refine ⟨by omega, ⟨by omega, by omega⟩,
    (1 - (X.m : ℝ) * X.J0 K / X.a) * (1 - Real.exp (-La' / 3)), mul_nonneg (by linarith) (by linarith), ?_, ?_⟩
  · intro τ hτ al hal be hbe
    obtain ⟨hal1, -⟩ := Finset.mem_Icc.1 hal
    obtain ⟨-, hbe2⟩ := Finset.mem_Icc.1 hbe
    have hala : (X.a : ℝ) ≤ al := by
      have : X.a ≤ al := by omega
      exact_mod_cast this
    have hal0 : 0 < al := by
      have : (0 : ℝ) < al := by linarith
      exact_mod_cast this
    have hbeR : (be : ℝ) ≤ X.bu + Z := by
      have a1 : (be : ℝ) ≤ (X.ub : ℝ) + τ := by exact_mod_cast hbe2
      have a2 : (X.ub : ℝ) ≤ X.bu := Nat.floor_le Wf.bunn
      have a3 : (τ : ℝ) ≤ X.ccl := by exact_mod_cast hτ
      linarith
    have hcond : (be : ℝ) + ((⌊La' * X.b' / ((X.m : ℝ) + 1)⌋₊ + 1 : ℕ) : ℝ) + (X.m : ℝ) + 1 ≤ 2 * X.b' := by
      have a1 : ((⌊La' * X.b' / ((X.m : ℝ) + 1)⌋₊ : ℕ) : ℝ) ≤ 2 * Z := by
        have : ((⌊La' * X.b' / ((X.m : ℝ) + 1)⌋₊ : ℕ) : ℝ) = (X.Jn K : ℝ) := by
          unfold Dat.Jn
          rw [hJ0]
          rfl
        rw [this]
        linarith
      push_cast
      have := Wf.bule
      linarith
    have key := Formalism.CountingSumsFrames.Top.densityLower X.m al be La' X.b' hm5 hal0 hb hLa'0 hcond
    have e1 : (X.m : ℝ) * (La' * X.b' / ((X.m : ℝ) + 1)) = (X.m : ℝ) * X.J0 K := by rw [hJ0]; rfl
    have e2 : ⌊La' * X.b' / ((X.m : ℝ) + 1)⌋₊ = X.Jn K := by
      unfold Dat.Jn
      rw [hJ0]
      rfl
    rw [e1, e2] at key
    refine le_trans ?_ key
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    have : (X.m : ℝ) * X.J0 K / al ≤ (X.m : ℝ) * X.J0 K / X.a := div_le_div_of_nonneg_left hmJ0 ha0 hala
    linarith
  · rw [cA, cB]
    push_cast
    have := dens_abs X.N hN1n ((X.m : ℝ) * X.J0 K / X.a) (Real.exp (-La' / 3)) ((X.Wa 0).card : ℝ)
      ((X.Wb 0).card : ℝ) ((X.Jn K + X.ccl : ℕ) : ℝ) hx10 hx20 hwaR hwbR he0 (by
        have e : (X.N : ℝ) * ((X.m : ℝ) * X.J0 K / X.a + Real.exp (-La' / 3) +
            ((X.Jn K + X.ccl : ℕ) : ℝ) / ((X.Wa 0).card : ℝ) + ((X.Jn K + X.ccl : ℕ) : ℝ) / ((X.Wb 0).card : ℝ)) =
            (X.N : ℝ) * ((X.m : ℝ) * X.J0 K / X.a) + (X.N : ℝ) * Real.exp (-La' / 3) +
            (X.N : ℝ) * (((X.Jn K + X.ccl : ℕ) : ℝ) / ((X.Wa 0).card : ℝ)) +
            (X.N : ℝ) * (((X.Jn K + X.ccl : ℕ) : ℝ) / ((X.Wb 0).card : ℝ)) := by ring
        rw [e]
        linarith)
    push_cast at this
    exact this

end Formalism.MainNotions.flipOneThree.Pf

end
