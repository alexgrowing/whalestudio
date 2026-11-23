import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NeSumLe

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

theorem price_linear_combination_le (n N rr w2 η cg NM b1 jt : ℝ) (hn : 0 ≤ n) (hN : 0 ≤ N) (hr : 0 ≤ rr) (hcg : 0 ≤ cg) (hjt : jt ≤ NM) :
    n * (rr * (w2 + η + cg)) + N * (rr * (2 * b1)) + n * rr * jt ≤
      rr * (N * (2 * b1 + cg) + n * (w2 + η + cg + NM)) := by
  nlinarith [mul_nonneg (mul_nonneg hr hN) hcg, mul_nonneg (mul_nonneg hn hr) (sub_nonneg.mpr hjt)]

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

section Orbit

variable (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (hT : GatTies D) (hL : Formalism.MainNotions.G.LatTied hT X Y)
  (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  (t0 : Formalism.MainNotions.G.HH D) (ht0 : t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w))

include hL ht0 in
theorem ne_b_top (hS : Formalism.MainNotions.SizesAt L) (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0)))
    (hs : s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0)) :
    L.sc.b' ≤ ((Y.Fl u w hg).b (Y.vOf u w hg t0) s : ℝ) ∧
      ((Y.Fl u w hg).b (Y.vOf u w hg t0) s : ℝ) ≤ 5 / 4 * L.sc.b' := by
  obtain ⟨_, h2, h3, _⟩ := ((hL u w hg).2.2.2.2.2.2 t0 ht0).2 s
  rw [(h3 hs).2]
  unfold Formalism.MainNotions.G.bL
  rw [dif_pos (h2.1 hs)]
  exact ⟨L.bT_ge _, ne_bT_le hS _⟩

include hL ht0 in
theorem ne_a_top (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0)))
    (hs : s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0)) :
    ((Y.Fl u w hg).a (Y.vOf u w hg t0) s : ℝ) ≤ 2 * L.sc.a := by
  obtain ⟨_, h2, h3, _⟩ := ((hL u w hg).2.2.2.2.2.2 t0 ht0).2 s
  rw [(h3 hs).1]
  unfold Formalism.MainNotions.G.aL
  rw [dif_pos (h2.1 hs)]
  exact ne_aT_le _

end Orbit

theorem ne_rG_lt (hS : Formalism.MainNotions.SizesAt L) (h : 34 < L.sc.x * L.sc.eps) : Formalism.MainNotions.G.rG L.sc < D.R.k := by
  have he := L.sc.eps_pos
  have he2 := L.sc.eps_lt
  have hx1 := L.sc.one_lt_alt
  have hK : Formalism.MainNotions.SizeK L := hS.2.2.1
  obtain ⟨hk, -⟩ := hK
  have hexp : (2 : ℝ) ≤ 9 / 2 + 10 * L.sc.eps - Formalism.MainNotions.szTh L := by
    simp only [Formalism.MainNotions.szTh]; linarith
  have hx2 : L.sc.x ^ (2 : ℝ) ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps - Formalism.MainNotions.szTh L) :=
    Real.rpow_le_rpow_of_exponent_le hx1.le hexp
  have hsq : L.sc.x ^ (2 : ℝ) = L.sc.x * L.sc.x := by rw [Real.rpow_two, sq]
  set E := 1 / L.sc.eps with hE
  have hEpos : 0 < E := by positivity
  have hxe : 34 * E < L.sc.x := by
    rw [hE, mul_one_div, div_lt_iff₀ he]; linarith
  have hinv : 52 < E := by
    rw [hE, lt_div_iff₀ he]; linarith
  have hsq2 : 34 * E * (34 * E) ≤ L.sc.x * L.sc.x :=
    mul_self_le_mul_self (by positivity) hxe.le
  have hv : 8 * (Formalism.MainNotions.G.hG L.sc + 2) / L.sc.eps = 32 * E + 64 := by
    rw [hE]; simp only [Formalism.MainNotions.G.hG]; field_simp; ring
  have hv0 : 0 ≤ 8 * (Formalism.MainNotions.G.hG L.sc + 2) / L.sc.eps := by rw [hv]; positivity
  have hc := Nat.ceil_lt_add_one hv0
  have hq : 32 * E + 66 ≤ 34 * E * (34 * E) := by nlinarith
  have h1 : (⌈8 * (Formalism.MainNotions.G.hG L.sc + 2) / L.sc.eps⌉₊ : ℝ) + 1 < 32 * E + 66 := by
    linarith [hc, hv]
  have h2 : 32 * E + 66 ≤ (D.R.k : ℝ) := by
    calc 32 * E + 66 ≤ 34 * E * (34 * E) := hq
      _ ≤ L.sc.x * L.sc.x := hsq2
      _ = L.sc.x ^ (2 : ℝ) := hsq.symm
      _ ≤ _ := hx2
      _ ≤ _ := hk
  unfold Formalism.MainNotions.G.rG Formalism.MainNotions.G.KG
  have hfin : ((⌈8 * (Formalism.MainNotions.G.hG L.sc + 2) / L.sc.eps⌉₊ + 1 : ℕ) : ℝ) < (D.R.k : ℝ) := by
    push_cast
    exact lt_of_lt_of_le h1 h2
  exact_mod_cast hfin

def priceThreshold : ℝ := 9

theorem price_threshold_ge_nine : 9 ≤ priceThreshold := by norm_num [priceThreshold]

open Classical in

theorem price_bound_small_primes : PriceBoundSmallPrimes := by
  intro D L X Y K hK hS hT hL u w hg hp t0 ht0 j hj
  obtain ⟨hrk, hx2⟩ := hK
  have hr : (D.gat u w hg).P.r = Formalism.MainNotions.G.rG L.sc := by rw [(hL u w hg).2.2.2.1, if_pos hp]
  have ht : (Y.Fl u w hg).t = D.R.t := (hL u w hg).2.1
  have hc : ((Y.Fl u w hg).c : ℝ) ≤ Formalism.MainNotions.G.cG L := (hL u w hg).2.2.1
  have hinj := nc_iota_inj X Y hT hL u w hg t0 ht0
  have hm := nc_m_ge hT u w hg
  have hk := hT.gat_k u w hg
  have hno : ¬ ((D.gat u w hg).P.m + 1 ≤ Formalism.MainNotions.G.rG L.sc) := by omega
  have hr0 : (0 : ℝ) ≤ (Formalism.MainNotions.G.rG L.sc : ℝ) := Nat.cast_nonneg _
  have hw := ne_w''_nonneg (L := L)
  have hη := L.etaSz_pos
  have hcG := nc_cG_nonneg (L := L)
  have hb' := L.sc.b'_pos
  rw [hr]
  have h1 := ne_abs (Y.Fl u w hg).t (Formalism.MainNotions.G.rG L.sc) j ((Y.Fl u w hg).TT (Y.vOf u w hg t0))
    ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0)) ((Y.Fl u w hg).w (Y.vOf u w hg t0))
    ((Formalism.MainNotions.G.rG L.sc : ℝ) * (L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L))
    ((Formalism.MainNotions.G.rG L.sc : ℝ) * (2 * L.sc.b'))
    (by positivity) (by positivity)
    (fun s _ => by
      have hsum := ne_sum_le (Y.Fl u w hg) (Y.vOf u w hg t0) s (Formalism.MainNotions.G.rG L.sc) hm (fun hs => by
        have h0 := (ne_b_top X Y hT hL u w hg t0 ht0 hS s hs).1
        have : (0 : ℝ) ≤ ((Y.Fl u w hg).b (Y.vOf u w hg t0) s : ℝ) := by linarith
        exact_mod_cast this)
      rw [if_neg (fun h => hno h.2)] at hsum
      have h7 := mul_le_mul_of_nonneg_left hc hr0
      have h11 := mul_nonneg hr0 hw
      by_cases hs : s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0)
      · rw [if_pos hs]
        have hwt := ne_w_top X Y hT hL u w hg t0 ht0 j hj s hs
        have hb := (ne_b_top X Y hT hL u w hg t0 ht0 hS s hs).2
        have hx : L.sc.b' / L.sc.x ≤ L.sc.b' / 2 := div_le_div_of_nonneg_left hb'.le (by norm_num) hx2
        have h5 := mul_le_mul_of_nonneg_left
          (show ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) ≤ 2 * L.sc.b' + L.etaSz by linarith) hr0
        nlinarith [h5, h7, hsum, h11]
      · rw [if_neg hs]
        have hwn := ne_w_non X Y hT hL u w hg t0 ht0 j hj s hs
        have h5 := mul_le_mul_of_nonneg_left hwn hr0
        nlinarith [h5, h7, hsum])
  refine le_trans h1 ?_
  unfold Formalism.MainNotions.G.Pr Formalism.MainNotions.G.Nv
  rw [if_neg (not_le.2 hp), nc_topsOn X Y hT hL u w hg t0 ht0, Finset.card_image_of_injective _ hinj,
    ne_nP X Y hT hL u w hg t0 ht0, ht]
  have hN := ne_Nm (D := D) j hj
  have hfin := price_linear_combination_le ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) (((Y.Fl u w hg).TT (Y.vOf u w hg t0)).card : ℝ)
    (Formalism.MainNotions.G.rG L.sc : ℝ) (L.sc.w'' D.R.n) L.etaSz (Formalism.MainNotions.G.cG L) (Formalism.MainNotions.G.Nm D) L.sc.b'
    ((j : ℝ) * ((D.R.t : ℝ) + 1) / 2) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hr0 hcG hN
  have e : ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) * (Formalism.MainNotions.G.rG L.sc : ℝ) * (j : ℝ) * ((D.R.t : ℝ) + 1) / 2 =
      ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) * (Formalism.MainNotions.G.rG L.sc : ℝ) * ((j : ℝ) * ((D.R.t : ℝ) + 1) / 2) := by ring
  rw [e]
  exact hfin

theorem priceBoundLargePrimes_priceThreshold : PriceBoundLargePrimes priceThreshold :=
  fun D L X Y K hK => price_bound_large_primes D L X Y K (by linarith [price_threshold_ge_nine])

theorem ne_priceThreshold : PriceBound priceThreshold :=
  priceBound_of_largePrimes_of_smallPrimes priceThreshold priceBoundLargePrimes_priceThreshold price_bound_small_primes

theorem exists_priceBound : ∃ C₀ : ℝ, 9 ≤ C₀ ∧ PriceBound C₀ :=
  ⟨priceThreshold, price_threshold_ge_nine, ne_priceThreshold⟩

theorem numericalComparisonUniform_of_size (hS : nd_NeedSize) : Formalism.MainNotions.FormalGroupSystem.NumericalComparisonUniform :=
  numerical_closed_of_threshold priceThreshold price_threshold_ge_nine (nc_need3_of priceThreshold hS ne_priceThreshold)

end Formalism.MainNotions.FormalGroupSystem.Pf
