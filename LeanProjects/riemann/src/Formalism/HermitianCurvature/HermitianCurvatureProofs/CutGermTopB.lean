import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopCore

namespace Formalism.FourierDecayAlt.P.CutBP.GT

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.GermRateSplit Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

def l1T (m : ℕ) : ℂ := (-1) ^ (m + 3) / Complex.I ^ (m + 2)

def l2T (m : ℕ) : ℂ := Complex.I * l1T m

theorem norm_l1T (m : ℕ) : ‖l1T m‖ = 1 := by
  simp [l1T]

theorem top_base_ne_zero (m : ℕ) : l1T m ≠ 0 := by
  intro h
  simpa [h] using norm_l1T m

theorem norm_l2T (m : ℕ) : ‖l2T m‖ = 1 := by
  rw [l2T, norm_mul, Complex.norm_I, norm_l1T, one_mul]

theorem top_root_ne_zero (m : ℕ) : l2T m ≠ 0 := by
  intro h
  simpa [h] using norm_l2T m

theorem top_root_pow_eq (m : ℕ) : l2T m ^ (m + 2) = (-1) ^ (m + 3) * l1T m ^ (m + 1) := by
  have hI : Complex.I ^ (m + 2) ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  have h1 : Complex.I ^ (m + 2) * l1T m = (-1) ^ (m + 3) := by
    rw [l1T, mul_div_cancel₀ _ hI]
  calc l2T m ^ (m + 2) = (Complex.I ^ (m + 2) * l1T m) * l1T m ^ (m + 1) := by
        rw [l2T]
        ring
    _ = (-1) ^ (m + 3) * l1T m ^ (m + 1) := by rw [h1]

theorem psi_l (m : ℕ) (w : ℂ) : G.psi U.betaU (l2T m / l1T m * w) = conj (G.psi ((2 : ℝ) : ℂ) w) := by
  have hl : l2T m / l1T m = Complex.I := by
    rw [l2T, mul_div_assoc, div_self (top_base_ne_zero m), mul_one]
  have key : U.betaU * (Complex.I * w) = -(((2 : ℝ) : ℂ) * w) := by
    simp only [U.betaU, Formalism.QuantumDeterminants.cStd]
    push_cast
    linear_combination (2 * w) * Complex.I_sq
  rw [hl, G.psi, G.psi, key, ← Complex.exp_conj]
  congr 1
  apply Complex.ext <;> simp

theorem const_match1 (k r : ℕ) (TT : ℝ) (b s : ℕ) (hb : 1 ≤ b) (hs : 2 ≤ s) (hbs : b + s = r + 2) (hk : 1 ≤ k)
    (h : C.LPt) (hsz : D.ptSize h = b - 1) :
    ∃ Kh : ℝ,
      (∀ x D : ℂ, x ≠ 0 → D ≠ 0 →
        ‖x‖ ^ (s - 1) * √(TBB.nPt k r TT (h ++ [(s - 1, x⁻¹), (1, x ^ (s - 1) * D)])) *
            (qU ^ ((s - 1) + (Fintype.card (G.UT (s - 1)) + (s - 1))))⁻¹ =
          Kh * ‖D‖ ^ (k - 1) * ‖x⁻¹‖ ^ ((s - 1) ^ 2) *
            (√((Complex.normSq (x ^ (s - 1) * D) - TT) ^ (k - 1)) / ‖x ^ (s - 1) * D‖ ^ (k - 1))) ∧
      (∀ u : ℂ, u ≠ 0 →
        Real.pi ^ (s - 1) * ((s : ℝ) * ‖u‖ ^ (s - 1))⁻¹ * √(TBB.nPt k r TT (h ++ [(s, u)])) *
            (qU ^ Fintype.card (G.UT s))⁻¹ =
          Kh * ‖u ^ s‖ ^ (k - 1) * ((s : ℝ)⁻¹ * ‖u‖ ^ ((s - 1) ^ 2))) := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 2 := ⟨s - 2, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain rfl : r = c + m + 1 := by omega
  rw [show c + 1 - 1 = c by omega] at hsz
  rw [show m + 2 - 1 = m + 1 by omega, show k' + 1 - 1 = k' by omega]
  have hsing : ∀ (GG : ℝ) (bb ss : ℕ) (t : ℂ), C.nAux (k' + 1) (c + m + 1) GG (fun _ _ => 1) bb [(ss, t)] =
      (if bb + ss - 1 = c + m + 1 + 1 ∧ ss = 1 then GG ^ (k' + 1 - 1)
        else ((1 : ℝ) * ‖t‖) ^ (2 * (ss : ℤ) * (C.Mlev (k' + 1) (c + m + 1) (bb + ss - 1) + ss - 3))) := by
    intro GG bb ss t
    simp only [C.nAux, mul_one]
  have hpos : ∀ (l : C.LPt) (bb : ℕ), 0 ≤ C.nAux (k' + 1) (c + m + 1) 0 (fun _ _ => 1) bb l := by
    intro l
    induction l with
    | nil => intro bb; simp [C.nAux]
    | cons a l ih =>
      intro bb
      obtain ⟨ss, t⟩ := a
      simp only [C.nAux]
      refine mul_nonneg ?_ (ih _)
      split_ifs
      · positivity
      · exact zpow_nonneg (by positivity) _
  set N : ℝ := C.nAux (k' + 1) (c + m + 1) 0 (fun _ _ => 1) 1 h with hNdef
  have hN0 : 0 ≤ N := hpos h 1
  have hind : ∀ GG : ℝ, C.nAux (k' + 1) (c + m + 1) GG (fun _ _ => 1) 1 h = N := fun GG =>
    PBD.weight_product_indep_of_real_parameter _ _ GG 0 _ h 1 le_rfl (by rw [hsz]; omega)
  have hq : qU ≠ 0 := by rw [qU_eq]; positivity
  have hcard : Fintype.card (G.UT (m + 2)) = Fintype.card (G.UT (m + 1)) + (m + 1) := by
    rw [G5.card_UT, G5.card_UT, Finset.sum_range_succ]
  refine ⟨√N * (qU ^ ((m + 1) + (Fintype.card (G.UT (m + 1)) + (m + 1))))⁻¹, fun x d0 hx hD => ?_,
    fun u hu => ?_⟩
  · have hL : h ++ [(m + 1, x⁻¹), (1, x ^ (m + 1) * d0)] =
        (h ++ [(m + 1, x⁻¹)]) ++ [(1, x ^ (m + 1) * d0)] := by simp
    have hGG : FourierDecayAlt.D.ptGG TT (h ++ [(m + 1, x⁻¹), (1, x ^ (m + 1) * d0)]) =
        Complex.normSq (x ^ (m + 1) * d0) - TT := by
      simp [FourierDecayAlt.D.ptGG, FourierDecayAlt.D.ptLast]
    have hsz2 : FourierDecayAlt.D.ptSize (h ++ [(m + 1, x⁻¹)]) = c + (m + 1) := by
      simp [FourierDecayAlt.D.ptSize] at hsz ⊢
      omega
    have hn : TBB.nPt (k' + 1) (c + m + 1) TT (h ++ [(m + 1, x⁻¹), (1, x ^ (m + 1) * d0)]) =
        N * ‖x‖⁻¹ ^ (((m + 1) * (k' + m + 2)) * 2) * (Complex.normSq (x ^ (m + 1) * d0) - TT) ^ k' := by
      rw [TBB.nPt, hGG, hL, PBD.weight_product_append, PBD.weight_product_append, hind, hsz, hsz2, hsing, hsing]
      rw [if_neg (show ¬(1 + c + (m + 1) - 1 = c + m + 1 + 1 ∧ m + 1 = 1) by omega),
        if_pos (show 1 + (c + (m + 1)) + 1 - 1 = c + m + 1 + 1 ∧ 1 = 1 by omega),
        one_mul, norm_inv, show k' + 1 - 1 = k' by omega, ← zpow_natCast (‖x‖⁻¹)]
      congr 3
      simp only [C.Mlev]
      push_cast [Nat.cast_sub (show 1 ≤ 1 + c + (m + 1) by omega)]
      ring
    have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    have hD' : ‖d0‖ ≠ 0 := norm_ne_zero_iff.2 hD
    rw [hn, Real.sqrt_mul (mul_nonneg hN0 (by positivity)), Real.sqrt_mul hN0, pow_mul,
      Real.sqrt_sq (by positivity), norm_inv, norm_mul, norm_pow, mul_pow]
    simp only [inv_pow, inv_inv]
    field_simp
    ring
  · have hsz3 : FourierDecayAlt.D.ptSize h = c := hsz
    have hn : TBB.nPt (k' + 1) (c + m + 1) TT (h ++ [(m + 2, u)]) =
        N * ‖u‖ ^ (((m + 2) * (k' + m + 1)) * 2) := by
      rw [TBB.nPt, PBD.weight_product_append, hind, hsz3, hsing,
        if_neg (show ¬(1 + c + (m + 2) - 1 = c + m + 1 + 1 ∧ m + 2 = 1) by omega),
        one_mul, ← zpow_natCast (‖u‖)]
      congr 2
      simp only [C.Mlev]
      push_cast [Nat.cast_sub (show 1 ≤ 1 + c + (m + 2) by omega)]
      ring
    have hu' : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu
    rw [hn, Real.sqrt_mul hN0, pow_mul, Real.sqrt_sq (by positivity), norm_pow, hcard, qU_eq]
    simp only [inv_pow, inv_inv]
    field_simp
    ring

section core

theorem top_level_germ_leading : TopCore1 := by
  intro Wp Wq _ _ _ _ _ _ P p F' hF' N b s hb hs hbs h hh K hK hK0
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 2 := ⟨s - 2, by omega⟩
  have hszH : D.ptSize h = b - 1 := hh.2
  have hk : 1 ≤ P.k := by have := p.hl.2.2; omega
  have hTT : 0 < TBB.TTp p := mul_pos p.T.base.T_pos p.T.base.T'_pos
  obtain ⟨ε0, hε0, hεG⟩ := hF'.2.2
  have hsmall : ∀ q : C.LPt, p.V F' q ≠ 0 → ε0 ≤ D.ptG (TBB.TTp p) P.r q := by
    intro q hq
    by_contra hlt
    exact hq (PBO.vecV_zero_small p.T.base p.ν' p.m₀ hεG q (not_le.1 hlt))
  obtain ⟨Φ0, hΦs, hΦc, hΦd, hΦV⟩ := phi_zero_hermitian_curvature Wp Wq P p F' hF'
  obtain ⟨σh, dh, Ψ0, hdh, hΨ0, hblk, hlng⟩ :=
    vec_om (p.V F') Φ0 ⟨hΦs, hΦc, hΦd⟩ (fun a σ d ha hm => hΦV a σ d ha hm) h hh.1 m (by omega)
  have hlng' : ∀ z : ℂ, z ≠ 0 → p.V F' (h ++ [(m + 2, z)]) =
      (((qU ^ Fintype.card (G.UT (m + 1 + 1)))⁻¹ : ℝ) : ℂ) • G.OmLong U.betaU (m + 1) (U.PhiTop (p := D.ptSize h) (s := m + 1 + 1) U.betaU σh dh Ψ0) (z) := hlng
  have hqE : ∀ n : ℕ, (((qU ^ n)⁻¹ : ℝ) : ℂ) ≠ 0 := fun n => by
    exact_mod_cast (inv_pos.2 (pow_pos qU_pos n)).ne'
  obtain ⟨Kh, hc1, hc2⟩ := const_match1 P.k P.r (TBB.TTp p) b (m + 2) hb hs hbs hk h hszH
  rw [show m + 2 - 1 = m + 1 by omega] at hc1 hc2
  set K' : Set ℂ := (fun d => d / l1T m ^ (m + 1)) '' K with hK'def
  have hK' : IsCompact K' := hK.image (continuous_id.div_const _)
  have hK'0 : (0 : ℂ) ∉ K' := by
    rintro ⟨d, hd, hd0⟩
    have : d = 0 := by simpa [top_base_ne_zero m] using hd0
    exact hK0 (this ▸ hd)
  obtain ⟨MK, hMK⟩ := hK'.isBounded.exists_norm_le
  obtain ⟨mK, hmK, hball⟩ := Metric.isOpen_iff.1 hK'.isClosed.isOpen_compl 0 hK'0
  have hmKle : ∀ y ∈ K', mK ≤ ‖y‖ := by
    intro y hy
    by_contra hlt
    exact hball (by simpa [Metric.mem_ball, dist_zero_right] using not_le.1 hlt) hy
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℂ → ℂ → ℝ, ∀ x y : ℂ, ρ x y =
      √((Complex.normSq (x ^ (m + 1) * y) - TBB.TTp p) ^ (P.k - 1)) / ‖x ^ (m + 1) * y‖ ^ (P.k - 1) *
        √((Complex.normSq (x ^ (m + 1) * y) / (Complex.normSq (x ^ (m + 1) * y) - TBB.TTp p)) ^ N) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨C0, hC0⟩ := germ_core m (D.ptSize h) σh dh hdh Ψ0 hΨ0 (l1T m) (l2T m) (top_base_ne_zero m) (top_root_pow_eq m) 2
    (psi_l m) K' hK' hK'0 ρ (√(((ε0 / (max (Complex.normSq (D.ptMatN h (D.ptSize h)).det) 1 * ‖l1T m‖ ^ (2 * (m + 1)) * (max MK 1) ^ 2))⁻¹) ^ N))
    ((((P.k - 1 : ℕ) : ℝ) + N * ((ε0 / (max (Complex.normSq (D.ptMatN h (D.ptSize h)).det) 1 * ‖l1T m‖ ^ (2 * (m + 1)) * (max MK 1) ^ 2))⁻¹) ^ N) * (TBB.TTp p / mK ^ 2)) (by
      intro x' y hx' hy hne
      have hy0 : y ≠ 0 := fun h0 => hK'0 (h0 ▸ hy)
      have ht0 : l1T m * x'⁻¹ ≠ 0 := mul_ne_zero (top_base_ne_zero m) (inv_ne_zero hx')
      have hc0 : x' ^ (m + 1) * y ≠ 0 := mul_ne_zero (pow_ne_zero _ hx') hy0
      have hV : p.V F' (h ++ [(m + 1, l1T m * x'⁻¹), (1, x' ^ (m + 1) * y)]) ≠ 0 := by
        rw [hblk _ _ ht0 hc0]
        exact smul_ne_zero (hqE _) hne
      have hG := hsmall _ hV
      rw [ptG_Px (TBB.TTp p) h (m + 1) (by omega) P.r (by omega)] at hG
      have hnc : Complex.normSq (x' ^ (m + 1) * y) = ‖x'‖ ^ (2 * (m + 1)) * ‖y‖ ^ 2 := by
        rw [Complex.normSq_mul, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, norm_pow]
        ring
      rw [hρdef]
      exact rho_bound (TBB.TTp p) ε0 (Complex.normSq (D.ptMatN h (D.ptSize h)).det) MK mK hTT hε0
        (Complex.normSq_nonneg _) hmK (P.k - 1) N m (l1T m) x' y (x' ^ (m + 1) * y) (top_base_ne_zero m) hx' hy0 hc0
        (hMK y hy) (hmKle y hy) hnc hG)
  obtain ⟨MD, hMD⟩ := hK.isBounded.exists_norm_le
  refine ⟨|Kh| * (max MD 1) ^ (P.k - 1) * C0, fun x hx d hd => ?_⟩
  have hd0 : d ≠ 0 := fun h0 => hK0 (h0 ▸ hd)
  have hx1 : x⁻¹ ≠ 0 := inv_ne_zero hx
  have hcne : x ^ (m + 1) * d ≠ 0 := mul_ne_zero (pow_ne_zero _ hx) hd0
  have ht : l1T m * (l1T m * x)⁻¹ = x⁻¹ := by field_simp [top_base_ne_zero m]
  have hcx : (l1T m * x) ^ (m + 1) * (d / l1T m ^ (m + 1)) = x ^ (m + 1) * d := by
    field_simp [top_base_ne_zero m]
    ring
  have hnx : ‖l1T m * x‖ = ‖x‖ := by rw [norm_mul, norm_l1T, one_mul]
  have hgerm := hC0 (l1T m * x) (mul_ne_zero (top_base_ne_zero m) hx) (d / l1T m ^ (m + 1)) ⟨d, hd, rfl⟩
  rw [ht, hcx, hnx] at hgerm
  have hT0 : (coT (m + 2) x none * (omT p N (ptT (m + 2) h x d none) : ℂ)) • p.V F' (ptT (m + 2) h x d none) =
      ((Kh * ‖d‖ ^ (P.k - 1) : ℝ) : ℂ) • (((‖x⁻¹‖ ^ ((m + 1) ^ 2) * ρ (l1T m * x) (d / l1T m ^ (m + 1)) : ℝ) : ℂ) •
        G.OmBlock U.betaU (m + 1) (U.PhiTop (p := D.ptSize h) (s := m + 1 + 1) U.betaU σh dh Ψ0) (x⁻¹) (x ^ (m + 1) * d)) := by
    show (((‖x‖ ^ (m + 1) : ℝ) : ℂ) * (omT p N (h ++ [(m + 1, x⁻¹), (1, x ^ (m + 1) * d)]) : ℂ)) •
        p.V F' (h ++ [(m + 1, x⁻¹), (1, x ^ (m + 1) * d)]) = _
    by_cases hB : G.OmBlock U.betaU (m + 1) (U.PhiTop (p := D.ptSize h) (s := m + 1 + 1) U.betaU σh dh Ψ0) (x⁻¹) (x ^ (m + 1) * d) = 0
    · rw [hblk _ _ hx1 hcne, hB]
      simp
    have hV : p.V F' (h ++ [(m + 1, x⁻¹), (1, x ^ (m + 1) * d)]) ≠ 0 := by
      rw [hblk _ _ hx1 hcne]
      exact smul_ne_zero (hqE _) hB
    have hG := hsmall _ hV
    have hw := wPt_Px (TBB.TTp p) h (m + 1) (by omega) P.r (by omega) x⁻¹ (x ^ (m + 1) * d)
      (lt_of_lt_of_le hε0 hG).ne'
    have e1 := hc1 x d hx hd0
    have hreal : ‖x‖ ^ (m + 1) * (√(TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(m + 1, x⁻¹), (1, x ^ (m + 1) * d)])) *
          √((Complex.normSq (x ^ (m + 1) * d) / (Complex.normSq (x ^ (m + 1) * d) - TBB.TTp p)) ^ N)) *
          (qU ^ ((m + 1) + (Fintype.card (G.UT (m + 1)) + (m + 1))))⁻¹ =
        Kh * ‖d‖ ^ (P.k - 1) * (‖x⁻¹‖ ^ ((m + 1) ^ 2) *
          (√((Complex.normSq (x ^ (m + 1) * d) - TBB.TTp p) ^ (P.k - 1)) / ‖x ^ (m + 1) * d‖ ^ (P.k - 1) *
            √((Complex.normSq (x ^ (m + 1) * d) / (Complex.normSq (x ^ (m + 1) * d) - TBB.TTp p)) ^ N))) := by
      linear_combination √((Complex.normSq (x ^ (m + 1) * d) / (Complex.normSq (x ^ (m + 1) * d) - TBB.TTp p)) ^ N) * e1
    rw [hblk _ _ hx1 hcne, smul_smul, smul_smul, hρdef, hcx]
    congr 1
    simp only [omT, hw]
    exact_mod_cast hreal
  have hroots : G.rootSet (m + 2) (epsT (m + 2) * d) = (G.rootSet (m + 2) (d / l1T m ^ (m + 1))).image (fun z => l2T m * z) := by
    ext z
    simp only [G.rootSet, Multiset.mem_toFinset, Polynomial.mem_nthRoots (show 0 < m + 2 by omega),
      Finset.mem_image]
    have hm1 : ((-1 : ℂ)) ^ (m + 3) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
    constructor
    · intro hz
      refine ⟨z / l2T m, ?_, by field_simp [top_root_ne_zero m]⟩
      rw [div_pow, hz, top_root_pow_eq, epsT]
      field_simp [top_base_ne_zero m]
      try ring
    · rintro ⟨w, hw, rfl⟩
      rw [mul_pow, top_root_pow_eq, hw, epsT]
      field_simp [top_base_ne_zero m]
      try ring
  have hsum : ∑ z ∈ G.rootSet (m + 2) (d / l1T m ^ (m + 1)), (coT (m + 2) x (some (l2T m * z)) *
        (omT p N (ptT (m + 2) h x d (some (l2T m * z))) : ℂ)) • p.V F' (ptT (m + 2) h x d (some (l2T m * z))) =
      -(((Kh * ‖d‖ ^ (P.k - 1) : ℝ) : ℂ) • (((m : ℂ) + 2)⁻¹ • ∑ z ∈ G.rootSet (m + 2) (d / l1T m ^ (m + 1)),
        (((‖l2T m * z‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) * conj (G.psi ((2 : ℝ) : ℂ) (((m : ℂ) + 2) * z * (l1T m * x)))) •
          G.OmLong U.betaU (m + 1) (U.PhiTop (p := D.ptSize h) (s := m + 1 + 1) U.betaU σh dh Ψ0) (l2T m * z))) := by
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun z hz => ?_
    have hz' : z ^ (m + 2) = d / l1T m ^ (m + 1) :=
      (Polynomial.mem_nthRoots (show 0 < m + 2 by omega)).1 (Multiset.mem_toFinset.1 hz)
    have hd' : d / l1T m ^ (m + 1) ≠ 0 := div_ne_zero hd0 (pow_ne_zero _ (top_base_ne_zero m))
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow (by omega)] at hz'
      exact hd' hz'.symm
    have hu : l2T m * z ≠ 0 := mul_ne_zero (top_root_ne_zero m) hz0
    have hud : ‖(l2T m * z) ^ (m + 2)‖ = ‖d‖ := by
      rw [mul_pow, top_root_pow_eq, hz']
      simp [norm_l1T]
    show (-(G.psi U.betaU (((m + 2 : ℕ) : ℂ) * (l2T m * z) * x) *
        ((Real.pi ^ (m + 1) * (((m + 2 : ℕ) : ℝ) * ‖l2T m * z‖ ^ (m + 1))⁻¹ : ℝ) : ℂ)) *
        (omT p N (h ++ [(m + 2, l2T m * z)]) : ℂ)) • p.V F' (h ++ [(m + 2, l2T m * z)]) = _
    by_cases hL : G.OmLong U.betaU (m + 1) (U.PhiTop (p := D.ptSize h) (s := m + 1 + 1) U.betaU σh dh Ψ0) (l2T m * z) = 0
    · rw [hlng' _ hu, hL]
      simp
    have hV : p.V F' (h ++ [(m + 2, l2T m * z)]) ≠ 0 := by
      rw [hlng' _ hu]
      exact smul_ne_zero (hqE _) hL
    have hG := hsmall _ hV
    have hw := PBL.wPt_big (TBB.TTp p) h (m + 2) (l2T m * z) P.r (by omega) (by omega)
      (lt_of_lt_of_le hε0 hG)
    have hpsi : G.psi U.betaU (((m + 2 : ℕ) : ℂ) * (l2T m * z) * x) =
        conj (G.psi ((2 : ℝ) : ℂ) (((m : ℂ) + 2) * z * (l1T m * x))) := by
      rw [← psi_l m]
      congr 1
      field_simp [top_base_ne_zero m]
      push_cast
      ring
    have e2 := hc2 (l2T m * z) hu
    rw [hud] at e2
    have e2c := congrArg (fun t : ℝ => (t : ℂ)) e2
    rw [hlng' _ hu, smul_smul, smul_smul, smul_smul, ← neg_smul]
    congr 1
    simp only [omT, hw, one_pow, Real.sqrt_one, mul_one, hpsi]
    push_cast at e2c ⊢
    linear_combination (-conj (G.psi ((2 : ℝ) : ℂ) (((m : ℂ) + 2) * z * (l1T m * x)))) * e2c
  have heq : ∑ j ∈ Finset.insertNone (G.rootSet (m + 2) (epsT (m + 2) * d)),
      (coT (m + 2) x j * (omT p N (ptT (m + 2) h x d j) : ℂ)) • p.V F' (ptT (m + 2) h x d j) =
      ((Kh * ‖d‖ ^ (P.k - 1) : ℝ) : ℂ) • (((‖x⁻¹‖ ^ ((m + 1) ^ 2) * ρ (l1T m * x) (d / l1T m ^ (m + 1)) : ℝ) : ℂ) • G.OmBlock U.betaU (m + 1) (U.PhiTop (p := D.ptSize h) (s := m + 1 + 1) U.betaU σh dh Ψ0) (x⁻¹) (x ^ (m + 1) * d) -
          ((m : ℂ) + 2)⁻¹ • ∑ z ∈ G.rootSet (m + 2) (d / l1T m ^ (m + 1)),
            (((‖l2T m * z‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) * conj (G.psi ((2 : ℝ) : ℂ) (((m : ℂ) + 2) * z * (l1T m * x)))) •
              G.OmLong U.betaU (m + 1) (U.PhiTop (p := D.ptSize h) (s := m + 1 + 1) U.betaU σh dh Ψ0) (l2T m * z)) := by
    rw [Finset.sum_insertNone, hroots,
      Finset.sum_image (fun a _ b _ hab => mul_left_cancel₀ (top_root_ne_zero m) hab)]
    beta_reduce
    rw [hT0, hsum, smul_sub, sub_eq_add_neg]
  rw [heq, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  have hdle : ‖d‖ ^ (P.k - 1) ≤ (max MD 1) ^ (P.k - 1) :=
    pow_le_pow_left₀ (norm_nonneg _) ((hMD d hd).trans (le_max_left _ _)) _
  have h0 : 0 ≤ C0 * ‖x‖⁻¹ := (norm_nonneg _).trans hgerm
  calc |Kh| * ‖d‖ ^ (P.k - 1) * ‖(((‖x⁻¹‖ ^ ((m + 1) ^ 2) * ρ (l1T m * x) (d / l1T m ^ (m + 1)) : ℝ) : ℂ) • G.OmBlock U.betaU (m + 1) (U.PhiTop (p := D.ptSize h) (s := m + 1 + 1) U.betaU σh dh Ψ0) (x⁻¹) (x ^ (m + 1) * d) -
          ((m : ℂ) + 2)⁻¹ • ∑ z ∈ G.rootSet (m + 2) (d / l1T m ^ (m + 1)),
            (((‖l2T m * z‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) * conj (G.psi ((2 : ℝ) : ℂ) (((m : ℂ) + 2) * z * (l1T m * x)))) •
              G.OmLong U.betaU (m + 1) (U.PhiTop (p := D.ptSize h) (s := m + 1 + 1) U.betaU σh dh Ψ0) (l2T m * z))‖
      ≤ |Kh| * (max MD 1) ^ (P.k - 1) * (C0 * ‖x‖⁻¹) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hdle (abs_nonneg _)) hgerm (norm_nonneg _)
          (mul_nonneg (abs_nonneg _) (pow_nonneg (le_trans zero_le_one (le_max_right _ _)) _))
    _ = |Kh| * (max MD 1) ^ (P.k - 1) * C0 * ‖x‖⁻¹ := by ring

end core

end

end Formalism.FourierDecayAlt.P.CutBP.GT
