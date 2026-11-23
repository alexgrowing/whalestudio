import Mathlib
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory.HCEntries

variable {D : D7} {L : SizeData₂ D}

theorem one_le_scL (L : SizeData₂ D) : 1 ≤ L.sc.L :=
  Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

theorem one_le_b (L : SizeData₂ D) : 1 ≤ L.sc.b :=
  Real.one_le_exp (by linarith [one_le_scL L])

theorem b'_pos (L : SizeData₂ D) : 0 < L.sc.b' := by
  have := L.sc.one_lt_alt
  have := one_le_b L
  unfold Scale.b' Scale.a Scale.X'
  positivity

theorem one_le_n (D : D7) : (1 : ℝ) ≤ D.R.n := by
  have : 1 ≤ D.R.n := by unfold Ranks.n; exact D.R.ord_pos
  exact_mod_cast this

theorem one_le_k (D : D7) : (1 : ℝ) ≤ D.R.k := by
  have : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  exact_mod_cast this

theorem one_le_letterBlockLength (D : D7) : (1 : ℝ) ≤ D.R.t := by
  have : 1 ≤ D.R.t := by have := D.R.three_m_lt_t; omega
  exact_mod_cast this

theorem eta_k_le (h : SizeEta L) : L.etaSz ≤ L.sc.b ∧ (D.R.k : ℝ) ≤ L.sc.b := by
  obtain ⟨h1, h2, -⟩ := h
  have hk := one_le_k D
  have ht := one_le_letterBlockLength D
  have hf : (1 : ℝ) ≤ D.R.f := by
    have := one_le_n D
    unfold Ranks.f
    push_cast
    linarith
  have hk3 : (D.R.k : ℝ) ≤ (D.R.k : ℝ) ^ 3 := le_self_pow₀ hk (by norm_num)
  have htf : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f := one_le_mul_of_one_le_of_one_le (one_le_pow₀ ht) hf
  have hP : (D.R.k : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 :=
    hk3.trans (le_mul_of_one_le_left (by positivity) htf)
  rw [le_div_iff₀ (by linarith)] at h2
  constructor <;> nlinarith

theorem b'_Sc_le (h : SizeLstar L) : L.sc.b' + L.Sc ≤ L.sc.b := by
  have hk := one_le_k D
  have ht := one_le_letterBlockLength D
  have hn := one_le_n D
  have hL := one_le_scL L
  have hb := one_le_b L
  have hS := L.Sc_pos
  have he := L.etaSz_pos
  have hm0 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  have hmt : (D.R.m : ℝ) ≤ D.R.t := by
    have : D.R.m ≤ D.R.t := by have := D.R.three_m_lt_t; omega
    exact_mod_cast this
  have h0 : 0 ≤ szlStar L := by unfold szlStar; positivity
  have h1 : szlStar L ≤ L.sc.b := by
    unfold szlStar
    rw [div_le_iff₀ (by positivity), mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    have e1 : (1 : ℝ) ≤ (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 := one_le_mul_of_one_le_of_one_le hk (one_le_pow₀ hn)
    have e2 : L.Sc + D.R.t + L.sc.L ≤ (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L) :=
      le_mul_of_one_le_left (by positivity) e1
    have e3 : 0 ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2 := by positivity
    linarith
  have h2 : 0 ≤ L.sc.b / szlStar L := div_nonneg (by linarith) h0
  linarith [h.1]

theorem bT_le (hLa : SizeLa L) (hR : SizeRho L) (hB : SizeBot L) (t : D.host.TT) :
    (L.bT t : ℝ) ≤ 5 / 4 * L.sc.b' := by
  have hx := L.sc.one_lt_alt
  have hk := one_le_k D
  have hb := b'_pos L
  have hLa0 : 0 ≤ L.LaG := le_trans (Real.rpow_nonneg (by linarith) _) hLa.1
  have hlog : 0 ≤ Real.log L.sc.x := Real.log_nonneg hx.le
  have h1 : 0 ≤ L.sc.x ^ szTh L * Real.log L.sc.x * L.LaG / D.R.k := by positivity
  have h2 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.le (by norm_num)
  unfold SizeRho at hR
  have h3 : szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / 4 := by
    have : 4 * szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k =
        4 * (szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
    linarith
  have h4 := hB t
  have h5 : szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
      (szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
  have h6 := mul_le_mul_of_nonneg_right h3 hb.le
  linarith

theorem aT_le (L : SizeData₂ D) (t : D.host.TT) : (L.aT t : ℝ) ≤ 2 * L.sc.x * L.sc.b := by
  have hx := L.sc.one_lt_alt
  have hb := one_le_b L
  have h1 := (L.aT_win t).2
  have h2 : (1 : ℝ) ≤ (D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2) :=
    one_le_mul_of_one_le_of_one_le (one_le_k D) (Real.one_le_rpow hx.le (by unfold Scale.A; norm_num))
  have h3 : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a :=
    div_le_self (by unfold Scale.a; positivity) h2
  have h4 : L.sc.a = L.sc.x * L.sc.b := rfl
  linarith

theorem exists_top {τ : D.what₂.Tau} (h : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces) :
    ∃ t : D.host.TT, (D.eTau τ : D.R.GG) = D.R.tau1 t := by
  unfold Host.topPlaces at h
  obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 h
  exact ⟨⟨t, ht⟩, hte.symm⟩

theorem wj_bounds (h : SizesAt L) (hx : 2 ≤ L.sc.x) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau) :
    0 ≤ wj D j τ ∧ wj D j τ ≤ 3 * L.sc.b := by
  obtain ⟨-, -, -, -, -, -, -, -, hLa, hR, hB, -, -, hE, -, hS, -⟩ := h
  have hb := one_le_b L
  have hb' := b'_pos L
  have he := (eta_k_le hE).1
  have hbb : L.sc.b' ≤ L.sc.b := by linarith [b'_Sc_le hS, L.Sc_pos]
  by_cases ha : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · obtain ⟨t, ht⟩ := exists_top ha
    obtain ⟨a1, a2⟩ := L.win_top j h1 h2 τ t ht
    have a3 := L.bT_ge t
    have a4 := bT_le hLa hR hB t
    have a5 : 0 ≤ L.sc.b' / L.sc.x := by positivity
    have a6 : L.sc.b' / L.sc.x ≤ L.sc.b' / 2 := div_le_div_of_nonneg_left hb'.le (by norm_num) hx
    constructor <;> linarith
  · by_cases hc : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · obtain ⟨a1, a2⟩ := L.win_thick j h1 h2 τ hc
      constructor <;> linarith
    · obtain ⟨a1, a2⟩ := L.win_thin j h1 h2 τ ⟨(D.eTau τ).2, ha, hc⟩
      have hn := one_le_n D
      have a5 : 0 ≤ L.sc.w'' D.R.n := by unfold Scale.w''; positivity
      have a6 : L.sc.w'' D.R.n ≤ L.sc.b' :=
        div_le_self hb'.le (one_le_mul_of_one_le_of_one_le (by linarith) hn)
      constructor <;> linarith

theorem b_bounds (h : SizesAt L) (hx : 2 ≤ L.sc.x) (τ : D.what₂.Tau) (j : Fin D.R.m) :
    -L.sc.b ≤ (((D.hc τ).b j : ℚ) : ℝ) ∧ (((D.hc τ).b j : ℚ) : ℝ) ≤ 3 * L.sc.b := by
  obtain ⟨a1, a2⟩ := wj_bounds h hx (j.1 + 1) (by omega) j.2 τ
  have hw : wj D (j.1 + 1) τ = (((D.hc τ).e j : ℚ) : ℝ) := by
    unfold wj
    rw [dif_pos (by simp)]
    rfl
  rw [hw] at a1 a2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hE, -⟩ := h
  have he := (eta_k_le hE).1
  have a3 := abs_le.1 (L.be_close τ j j)
  have a4 : (D.hc τ).b j ≤ (D.hc τ).e j := by
    have := (D.hc τ).gap_be j
    have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
    linarith
  have a5 : (((D.hc τ).b j : ℚ) : ℝ) ≤ (((D.hc τ).e j : ℚ) : ℝ) := by exact_mod_cast a4
  push_cast at a3
  constructor <;> linarith [a3.1]

theorem sigPar_bound (h : SizesAt L) (hx : 2 ≤ L.sc.x) (τ : D.what₂.Tau) (l : ℕ) :
    |((sigPar D τ l : ℚ) : ℝ)| ≤ 4 * L.sc.b := by
  have hb := one_le_b L
  have hS : L.Sc ≤ L.sc.b := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hS, -⟩ := h
    linarith [b'_Sc_le hS, b'_pos L]
  unfold sigPar
  split_ifs with h1 h2
  · obtain ⟨a1, a2⟩ := L.cloud_v τ ⟨l, h1⟩
    rw [abs_le]
    constructor <;> linarith
  · obtain ⟨a1, a2⟩ := b_bounds h hx τ ⟨_, h2⟩
    rw [abs_le]
    push_cast
    constructor <;> linarith
  · simp only [Rat.cast_zero, abs_zero]
    linarith

theorem u_bound (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (l : Fin D.R.k) : |(((D.hcW u τ).u l : ℚ) : ℝ)| ≤ 4 * L.sc.x * L.sc.b := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hm := D.R.two_le_m
  have hb := one_le_b L
  have hxb : 2 * L.sc.b ≤ L.sc.x * L.sc.b := mul_le_mul_of_nonneg_right hx (by linarith)
  have hb1 := b_bounds h hx τ ⟨0, by omega⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hE, -, hS, -⟩ := h
  have hkb := (eta_k_le hE).2
  have hS : L.Sc ≤ L.sc.b := by linarith [b'_Sc_le hS, b'_pos L]
  obtain ⟨r, hr⟩ := l
  rw [abs_le]
  by_cases h0 : r = 0
  · subst h0
    rw [D.hcW_first u τ hr]
    have h2 := L.cloud_v τ ⟨0, by omega⟩
    have h3 : (((D.hc τ).v ⟨0, by omega⟩ : ℚ) : ℝ) < (((D.hc τ).u ⟨0, hr⟩ : ℚ) : ℝ) := by
      exact_mod_cast (D.hc τ).u_gt_v ⟨0, by omega⟩
    refine ⟨by linarith [h2.1], ?_⟩
    by_cases ha : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · obtain ⟨t, ht⟩ := exists_top ha
      rw [(L.top_u τ t hr ht).1]
      linarith [aT_le L t]
    · have h1 := P.cloud_place_bound τ (by omega) ha
      push_cast at h1
      linarith [h2.2]
  · by_cases hl : r + 1 < D.R.k
    · have := L.cloud_u u τ ⟨r, hr⟩ (by show 1 ≤ r; omega) hl
      constructor <;> linarith [this.1, this.2]
    · obtain rfl : r = D.R.k - 1 := by omega
      rw [D.hcW_last u τ (by omega)]
      have h2 := L.cloud_v τ ⟨D.R.k - 2, by omega⟩
      have h3 : -(((D.hc τ).b ⟨0, by omega⟩ : ℚ) : ℝ) < (((D.hc τ).u ⟨D.R.k - 1, hr⟩ : ℚ) : ℝ) := by
        exact_mod_cast (D.hc τ).u_last_gt (by omega) (by omega)
      have h4 : (((D.hc τ).u ⟨D.R.k - 1, hr⟩ : ℚ) : ℝ) < (((D.hc τ).v ⟨D.R.k - 2, by omega⟩ : ℚ) : ℝ) := by
        have := (D.hc τ).v_gt_u ⟨D.R.k - 2, by omega⟩
        have e : (⟨D.R.k - 2 + 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, hr⟩ :=
          Fin.ext (by show D.R.k - 2 + 1 = D.R.k - 1; omega)
        simp only at this
        rw [e] at this
        exact_mod_cast this
      constructor <;> linarith [h2.2, hb1.2]

theorem entries : ∀ (eps : ℝ) (Fm : FamP eps), (∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, (∀ j ∈ SizeData₂.lifts (Fm.D x i), ∀ τ, 0 ≤ wj (Fm.D x i) j τ ∧ wj (Fm.D x i) j τ ≤ 3 * (Fm.L x i).sc.b ∧ wSz (Fm.D x i) j τ = wj (Fm.D x i) j τ) ∧ (∀ u τ (l : Fin (Fm.D x i).R.k), |((((Fm.D x i).hcW u τ).u l : ℚ) : ℝ)| ≤ 4 * x * (Fm.L x i).sc.b) ∧ (∀ τ l, |((sigPar (Fm.D x i) τ l : ℚ) : ℝ)| ≤ 4 * (Fm.L x i).sc.b)) := by
  intro eps Fm
  refine ⟨2, fun x hx2 hx i => ?_⟩
  have hS := Fm.sizes x hx i
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
  have h2 : 2 ≤ (Fm.L x i).sc.x := by rw [hsx]; exact hx2
  refine ⟨fun j hj τ => ?_, fun u τ l => ?_, fun τ l => sigPar_bound hS h2 τ l⟩
  · obtain ⟨h1, hm⟩ := Finset.mem_Icc.1 hj
    obtain ⟨a1, a2⟩ := wj_bounds hS h2 j h1 hm τ
    refine ⟨a1, a2, ?_⟩
    unfold wSz wj
    rw [dif_pos ⟨h1, hm⟩, dif_pos (by omega)]
  · have := u_bound hS (Fm.params x hx i) h2 u τ l
    rwa [hsx] at this

end GlobalTheory.HCEntries
