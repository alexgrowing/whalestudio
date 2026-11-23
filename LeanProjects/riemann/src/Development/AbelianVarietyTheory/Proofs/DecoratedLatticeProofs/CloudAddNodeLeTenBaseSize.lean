import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Formalism.SharpRestriction.ElevenLe
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.HostTorsionOrderLe
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX

namespace GlobalTheory

theorem cloud_add_node_le_ten_b : ∀ (C : Formalism.MainNotions.Inhab.FC) (cD ch : ℝ) (D : D7) (L : SizeData₂ D), Val C cD ch L →
    SizesAt L → L.sc.x ≤ L.sc.X' → ∀ τ : D.what₂.Tau,
    (∀ i j, (((D.hc τ).v i : ℚ) : ℝ) + (((D.hc τ).b j : ℚ) : ℝ) ≤ 10 * L.sc.b) ∧
      ∀ j j', (((D.hc τ).b j' : ℚ) : ℝ) - (((D.hc τ).b j : ℚ) : ℝ) ≤ 10 * L.sc.b := by
  intro C cD ch D L hV hS hxX τ
  obtain ⟨-, -, -, -, -, -, -, -, hLa, hRho, hBot, -, -, -, -, -, hDel, -, hBm, -⟩ := hS
  obtain ⟨hv, -, ⟨b1, hbj, htop, hthick, hthin⟩, -⟩ := hV.hc
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hL : 0 < L.sc.L := Real.rpow_pos_of_pos hx0 _
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp hL.le
  have hX'pos : 0 < L.sc.X' := Real.exp_pos _
  have hb'0 : 0 ≤ L.sc.b' := by
    unfold Scale.b' Scale.a; positivity
  have hb'b : L.sc.b' ≤ L.sc.b := by
    unfold Scale.b' Scale.a
    rw [div_le_iff₀ hX'pos]
    nlinarith
  have hwb : L.sc.w'' D.R.n ≤ L.sc.b := by
    unfold Scale.w''
    rcases Nat.eq_zero_or_pos D.R.n with hn | hn
    · simp [hn]; linarith
    · have h1 : (1:ℝ) ≤ D.R.n := by exact_mod_cast hn
      have : (1:ℝ) ≤ L.sc.x * D.R.n := by nlinarith
      exact (div_le_self hb'0 this).trans hb'b

  have hw : ((NumberField.Units.torsionOrder D.host.E : ℕ) : ℝ) ≤ L.sc.b := by
    have h1 := UpperTheory.Mu.host_torsionOrder_le D.host
    have hfk : D.R.f ≤ D.R.k := D.R.f_le_k
    have hkN : D.R.k ≤ D.R.N D.R.m := Nat.le_add_right _ _
    have hm2 := D.R.two_le_m
    have hm10 : 8 ≤ D.R.m ^ 10 := le_trans (by norm_num) (Nat.pow_le_pow_left hm2 10)
    have h2 : NumberField.Units.torsionOrder D.host.E ≤ D.R.k * (D.R.N D.R.m * D.R.m ^ 10) := by
      calc _ ≤ 8 * D.R.f ^ 2 := h1
        _ = D.R.f * (D.R.f * 8) := by ring
        _ ≤ _ := Nat.mul_le_mul hfk (Nat.mul_le_mul (hfk.trans hkN) hm10)
    have h3 : ((NumberField.Units.torsionOrder D.host.E : ℕ) : ℝ) ≤
        (D.R.k : ℝ) * ((D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10) := by exact_mod_cast h2
    have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
    have h4 := mul_le_mul_of_nonneg_left hDel.1 hk0
    have hD := hDel.2.2.2.2.1
    have hth : (1 : ℝ) ≤ L.sc.x ^ szTh L :=
      Real.one_le_rpow hx.le (by unfold szTh; linarith [L.sc.eps_pos])
    have hm1 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
    have h5 : (1 : ℝ) ≤ L.sc.x ^ szTh L * D.R.m := by nlinarith
    have hkD0 : (0 : ℝ) ≤ (D.R.k : ℝ) * (D.s.Del : ℝ) := le_trans (by positivity) h4
    have h6 := le_mul_of_one_le_left hkD0 h5
    have e : (L.sc.x ^ szTh L * D.R.m) * ((D.R.k : ℝ) * (D.s.Del : ℝ)) =
        L.sc.x ^ szTh L * D.R.m * D.R.k * (D.s.Del : ℝ) := by ring
    linarith

  have hbase : ((b1 τ : ℤ) : ℝ) ≤ 3 * L.sc.b := by
    by_cases htp : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 htp
      have h1 := htop τ ⟨t, ht⟩ hte.symm
      have h2 := hBot ⟨t, ht⟩
      have hLa0 : 0 ≤ L.LaG := le_trans (Real.rpow_pos_of_pos hx0 _).le hLa.1
      have hsec : 0 ≤ L.sc.x ^ szTh L * Real.log L.sc.x * L.LaG / D.R.k := by
        have := Real.log_nonneg hx.le
        have := Real.rpow_pos_of_pos hx0 (szTh L)
        positivity
      have hx2 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.le (by norm_num)
      have hq : szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / 4 := by
        have : 4 * szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k =
            4 * (szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
        unfold SizeRho at hRho
        linarith
      have hq' : szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k ≤ L.sc.b' / 4 := by
        have : szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
            (szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
        rw [this]; nlinarith
      have hfl : ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) ≤ L.sc.b' :=
        (Int.floor_le _).trans (div_le_self hb'0 hx.le)
      have : ((b1 τ : ℤ) : ℝ) = (L.bT ⟨t, ht⟩ : ℝ) + ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) := by
        rw [h1]; push_cast; ring
      linarith
    · by_cases hth : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
      · have hc := Int.ceil_lt_add_one L.sc.b
        have h := (hthick τ hth).2
        have hR : ((b1 τ : ℤ) : ℝ) < ((⌈L.sc.b⌉ : ℤ) : ℝ) + ((NumberField.Units.torsionOrder D.host.E : ℕ) : ℝ) := by
          exact_mod_cast h
        linarith
      · have h := hthin τ ⟨(D.eTau τ).2, htp, hth⟩
        have hc := Int.ceil_lt_add_one (L.sc.w'' D.R.n)
        rw [h]; linarith

  have hbR : ∀ j : Fin D.R.m, (((D.hc τ).b j : ℚ) : ℝ) = (b1 τ : ℝ) + (j.1 : ℝ) * (h0v L.sc ch : ℝ) := by
    intro j; rw [(hbj τ j).1]; push_cast; ring
  have hh0 : (0 : ℝ) ≤ (h0v L.sc ch : ℝ) := Nat.cast_nonneg _
  have hspan : ∀ j : Fin D.R.m, (j.1 : ℝ) * (h0v L.sc ch : ℝ) ≤ (b1 τ : ℝ) := by
    intro j
    have hm : 0 < D.R.m := j.pos
    have hB := hBm τ hm
    rw [hbR, hbR] at hB
    have hj : (j.1 : ℝ) ≤ ((D.R.m - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : j.1 ≤ D.R.m - 1)
    have := mul_le_mul_of_nonneg_right hj hh0
    simp only [Nat.cast_zero, zero_mul, add_zero] at hB
    linarith
  refine ⟨fun i j => ?_, fun j j' => ?_⟩
  · have hm : 0 < D.R.m := j.pos
    rw [hv τ i, hbR j]
    have hD := hDel.2.2.2.2.1
    rw [hV.Del_eq] at hD
    simp only [Rat.cast_natCast] at hD
    have hth : (1 : ℝ) ≤ L.sc.x ^ szTh L :=
      Real.one_le_rpow hx.le (by unfold szTh; linarith [L.sc.eps_pos])
    have hm1 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast hm
    have hDl0 : (0 : ℝ) ≤ (Delv L.sc cD : ℝ) := Nat.cast_nonneg _
    have hkD0 : (0 : ℝ) ≤ (D.R.k : ℝ) * (Delv L.sc cD : ℝ) := by positivity
    have hkD : (D.R.k : ℝ) * (Delv L.sc cD : ℝ) ≤ L.sc.b := by
      have h1 : (1 : ℝ) ≤ L.sc.x ^ szTh L * D.R.m := by nlinarith
      have : (D.R.k : ℝ) * (Delv L.sc cD : ℝ) ≤ (L.sc.x ^ szTh L * D.R.m) * ((D.R.k : ℝ) * (Delv L.sc cD : ℝ)) := by
        nlinarith
      have e : (L.sc.x ^ szTh L * D.R.m) * ((D.R.k : ℝ) * (Delv L.sc cD : ℝ)) =
          L.sc.x ^ szTh L * D.R.m * D.R.k * (Delv L.sc cD : ℝ) := by ring
      linarith
    have hki : ((D.R.k - 2 - i.1 : ℕ) : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast (by omega : D.R.k - 2 - i.1 ≤ D.R.k)
    simp only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
    have := mul_le_mul_of_nonneg_right hki (by positivity : (0:ℝ) ≤ 4 * (Delv L.sc cD : ℝ))
    have := hspan j
    nlinarith
  · rw [hbR j, hbR j']
    have h1 := hspan j'
    have h2 : 0 ≤ (j.1 : ℝ) * (h0v L.sc ch : ℝ) := by positivity
    linarith

end GlobalTheory
