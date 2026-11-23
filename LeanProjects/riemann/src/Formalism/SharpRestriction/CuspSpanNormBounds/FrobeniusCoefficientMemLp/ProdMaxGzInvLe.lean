import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.OneLeProdMax

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.S.Pv.HH

open Finset NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem absGz_le (Z : GramM D) {b C β T T' : ℝ} (hb : 0 < b) (hβ : 1 ≤ β) (hT0 : 0 ≤ T) (hT : T ≤ β)
    (hT0' : 0 ≤ T') (hT' : T' ≤ β) (hr : 1 ≤ D.R.rS) (τ : D.what₂.Tau) :
    |Cnt.Gz D T T' Z τ| ≤ 2 * β ^ 2 * (b ^ (C * (D.R.m : ℝ) ^ 2) * Formalism.MainNotions.GramProductBounds.Pt D b C Z τ) ^ 2 := by
  have hr1 : D.R.rS + 1 ∈ Finset.Icc 1 (D.R.rS + 1) := Finset.mem_Icc.2 ⟨by omega, le_rfl⟩
  have hr0 : D.R.rS ∈ Finset.Icc 1 (D.R.rS + 1) := Finset.mem_Icc.2 ⟨hr, by omega⟩
  have ha0 := Formalism.MainNotions.GramProductBounds.absDl_nonneg D Z (D.R.rS + 1) τ
  have hd0 := Formalism.MainNotions.GramProductBounds.absDl_nonneg D Z D.R.rS τ
  have ha := Formalism.MainNotions.GramProductBounds.absDl_le_Pt D (C := C) hb Z τ hr1
  have hd := Formalism.MainNotions.GramProductBounds.absDl_le_Pt D (C := C) hb Z τ hr0
  set X := b ^ (C * (D.R.m : ℝ) ^ 2) * Formalism.MainNotions.GramProductBounds.Pt D b C Z τ
  have hX0 : 0 ≤ X ^ 2 := sq_nonneg _
  have ha2 := pow_le_pow_left₀ ha0 ha 2
  have hd2 := pow_le_pow_left₀ hd0 hd 2
  have hc0 : 0 ≤ T * T' := mul_nonneg hT0 hT0'
  have hc : T * T' ≤ β ^ 2 := by rw [sq]; exact mul_le_mul hT hT' hT0' (by linarith)
  have hβ2 : 1 ≤ β ^ 2 := one_le_pow₀ hβ
  have hcd : T * T' * absDl D Z D.R.rS τ ^ 2 ≤ β ^ 2 * X ^ 2 := mul_le_mul hc hd2 (sq_nonneg _) (by positivity)
  have hcd0 : 0 ≤ T * T' * absDl D Z D.R.rS τ ^ 2 := by positivity
  have hXβ : X ^ 2 ≤ β ^ 2 * X ^ 2 := le_mul_of_one_le_left hX0 hβ2
  unfold Cnt.Gz
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (absDl D Z (D.R.rS + 1) τ)]

def Gbd (b C β : ℝ) (Z : GramM D) : ℝ := (2 * β ^ 2 * (b ^ (C * (D.R.m : ℝ) ^ 2)) ^ 2) ^ D.R.f * sizeZ D b C Z ^ 2

theorem prod_max_absGz_le (Z : GramM D) {b C β T T' : ℝ} (hb : 1 ≤ b) (hC : 0 ≤ C) (hβ : 1 ≤ β) (hT0 : 0 ≤ T)
    (hT : T ≤ β) (hT0' : 0 ≤ T') (hT' : T' ≤ β) (hr : 1 ≤ D.R.rS) :
    ∏ τ, max 1 |Cnt.Gz D T T' Z τ| ≤ Gbd D b C β Z := by
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hH : 1 ≤ b ^ (C * (D.R.m : ℝ) ^ 2) := Real.one_le_rpow hb (by positivity)
  have hf : (Finset.univ : Finset D.what₂.Tau).card = D.R.f := by rw [Finset.card_univ, D.what₂.card_Tau]
  have hP1 : ∀ τ, 1 ≤ Formalism.MainNotions.GramProductBounds.Pt D b C Z τ := fun τ => Formalism.MainNotions.GramProductBounds.one_le_prod_max _ _
  have step : ∀ τ, max 1 |Cnt.Gz D T T' Z τ| ≤
      (2 * β ^ 2 * (b ^ (C * (D.R.m : ℝ) ^ 2)) ^ 2) * Formalism.MainNotions.GramProductBounds.Pt D b C Z τ ^ 2 := by
    intro τ
    have h1 : 1 ≤ (2 * β ^ 2 * (b ^ (C * (D.R.m : ℝ) ^ 2)) ^ 2) * Formalism.MainNotions.GramProductBounds.Pt D b C Z τ ^ 2 := by
      have : 1 ≤ 2 * β ^ 2 * (b ^ (C * (D.R.m : ℝ) ^ 2)) ^ 2 := by
        have h2 : 1 ≤ β ^ 2 := one_le_pow₀ hβ
        have h3 : 1 ≤ (b ^ (C * (D.R.m : ℝ) ^ 2)) ^ 2 := one_le_pow₀ hH
        nlinarith
      exact one_le_mul_of_one_le_of_one_le this (one_le_pow₀ (hP1 τ))
    refine max_le h1 (le_trans (absGz_le D Z (C := C) hb0 hβ hT0 hT hT0' hT' hr τ) (le_of_eq ?_))
    ring
  calc ∏ τ, max 1 |Cnt.Gz D T T' Z τ| ≤ ∏ τ, ((2 * β ^ 2 * (b ^ (C * (D.R.m : ℝ) ^ 2)) ^ 2) *
        Formalism.MainNotions.GramProductBounds.Pt D b C Z τ ^ 2) :=
        Finset.prod_le_prod (fun τ _ => le_trans zero_le_one (le_max_left _ _)) (fun τ _ => step τ)
    _ = Gbd D b C β Z := by
        unfold Gbd
        rw [Finset.prod_mul_distrib, Finset.prod_const, hf, Finset.prod_pow, Formalism.MainNotions.GramProductBounds.sizeZ_eq]

theorem prod_max_Gz_le (Z : GramM D) {b C β T T' : ℝ} (hb : 1 ≤ b) (hC : 0 ≤ C) (hβ : 1 ≤ β) (hT0 : 0 ≤ T)
    (hT : T ≤ β) (hT0' : 0 ≤ T') (hT' : T' ≤ β) (hr : 1 ≤ D.R.rS) :
    ∏ τ, max 1 (Cnt.Gz D T T' Z τ) ≤ Gbd D b C β Z := by
  refine le_trans ?_ (prod_max_absGz_le D Z hb hC hβ hT0 hT hT0' hT' hr)
  apply Finset.prod_le_prod
  · intro τ _
    exact le_trans zero_le_one (le_max_left _ _)
  · intro τ _
    exact max_le_max le_rfl (le_abs_self _)

theorem embS_star (τ : D.what₂.Tau) (x : D.host.E) : embS D τ (star x) = starRingEnd ℂ (embS D τ x) := by
  unfold embS
  first
  | exact NumberField.IsCMField.complexEmbedding_complexConj _ _
  | exact NumberField.IsCMField.embedding_complexConj _ _
  | exact NumberField.IsCMField.map_complexConj _ _
  | exact (NumberField.IsCMField.complexEmbedding_complexConj (K := D.host.E) (D.host.emb _) x : _)

theorem frameExp_succ : frameExp D.R.rS (D.R.rS + 1) = frameExp D.R.rS D.R.rS := by
  unfold frameExp
  rw [Finset.sum_Icc_succ_top (by omega)]
  simp

def wG : ℝ := D.host.rdE ^ (-(2 * (frameExp D.R.rS D.R.rS : ℝ)))

private theorem one_le_host_rdE : 1 ≤ D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  apply Real.one_le_rpow _ (by positivity)
  have h := NumberField.discr_ne_zero D.host.E
  have h' : (1 : ℤ) ≤ |discr D.host.E| := Int.one_le_abs h
  have h'' : ((1 : ℤ) : ℝ) ≤ ((|discr D.host.E| : ℤ) : ℝ) := by exact_mod_cast h'
  simpa [Int.cast_abs] using h''

private theorem frameExp_self_le_succ_sq (r : ℕ) : frameExp r r ≤ (r + 1) ^ 2 := by
  unfold frameExp
  calc ∑ a ∈ Finset.Icc 1 r, (r + 1 - a) ≤ ∑ a ∈ Finset.Icc 1 r, (r + 1) :=
        Finset.sum_le_sum fun a _ => Nat.sub_le _ _
    _ = r * (r + 1) := by simp [Nat.card_Icc]
    _ ≤ (r + 1) ^ 2 := by nlinarith

theorem wG_pos : 0 < wG D := by
  unfold wG
  exact Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (one_le_host_rdE D)) _

theorem wG_le_one : wG D ≤ 1 := by
  unfold wG
  apply Real.rpow_le_one_of_one_le_of_nonpos (one_le_host_rdE D)
  have : (0 : ℝ) ≤ (frameExp D.R.rS D.R.rS : ℝ) := Nat.cast_nonneg _
  linarith

theorem wG_inv_le : (wG D)⁻¹ ≤ R1 D := by
  have h1 := one_le_host_rdE D
  have h0 : (0 : ℝ) ≤ D.host.rdE := by linarith
  unfold wG R1
  rw [Real.rpow_neg h0, inv_inv]
  apply Real.rpow_le_rpow_of_exponent_le h1
  have h2 := frameExp_self_le_succ_sq D.R.rS
  have h3 : ((frameExp D.R.rS D.R.rS : ℕ) : ℝ) ≤ ((D.R.rS : ℝ) + 1) ^ 2 := by exact_mod_cast h2
  linarith

theorem absGz_eq {u u' : D.what₂.Word} (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : FlagU D u')
    (τ : D.what₂.Tau) :
    |Cnt.Gz D (Tu D u) (Tu D u') (ZhatL (lf D F0) F') τ| = ‖embS D τ (Gval (lf D F0) F')‖ * wG D ^ 2 := by
  have e1 : ∀ x : D.host.E, embS D τ (x * star x) = ((Complex.normSq (embS D τ x) : ℝ) : ℂ) := by
    intro x; rw [map_mul, embS_star, Complex.mul_conj]
  have hG : embS D τ (Gval (lf D F0) F') =
      (((Complex.normSq (embS D τ (leadMinorE (ZhatL (lf D F0) F') (D.R.rS + 1)))) -
        ((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ) *
          Complex.normSq (embS D τ (leadMinorE (ZhatL (lf D F0) F') D.R.rS)) : ℝ) : ℂ) := by
    show embS D τ (Gflag (lf D F0).fl F'.fl) = _
    unfold Gflag Dl
    rw [map_sub, e1, map_mul, e1, map_mul, map_natCast, map_natCast]
    push_cast
    ring
  rw [hG, Complex.norm_real, Real.norm_eq_abs]
  unfold Cnt.Gz absDl absReal
  rw [frameExp_succ]
  simp only [Complex.normSq_eq_norm_sq]
  rw [← abs_of_pos (pow_pos (wG_pos D) 2), ← abs_mul]
  congr 1
  unfold wG
  ring

theorem prod_max_Gz_inv_le {u u' : D.what₂.Word} (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (F' : FlagU D u') (hγ : Gval (lf D F0) F' ∈ intS D) (hγ0 : Gval (lf D F0) F' ≠ 0)
    {b C β : ℝ} (hb : 1 ≤ b) (hC : 0 ≤ C) (hβ : 1 ≤ β) (hT : ((Tu D u : ℕ) : ℝ) ≤ β)
    (hT' : ((Tu D u' : ℕ) : ℝ) ≤ β) (hr : 1 ≤ D.R.rS) :
    ∏ τ, max 1 (Cnt.Gz D (Tu D u) (Tu D u') (ZhatL (lf D F0) F') τ)⁻¹ ≤
      (R1 D ^ 2) ^ D.R.f * (R1 D ^ 2) ^ D.R.f * Gbd D b C β (ZhatL (lf D F0) F') := by
  set Z := ZhatL (lf D F0) F'
  set γ := Gval (lf D F0) F'
  set s := wG D ^ 2 with hs
  have hs0 : 0 < s := pow_pos (wG_pos D) 2
  have hs1 : s ≤ 1 := pow_le_one₀ (wG_pos D).le (wG_le_one D)
  have hsi : 1 ≤ s⁻¹ := one_le_inv₀ hs0 |>.2 hs1
  have hsR : s⁻¹ ≤ R1 D ^ 2 := by
    rw [hs, ← inv_pow]; exact pow_le_pow_left₀ (inv_nonneg.2 (wG_pos D).le) (wG_inv_le D) 2
  have hf : (Finset.univ : Finset D.what₂.Tau).card = D.R.f := by rw [Finset.card_univ, D.what₂.card_Tau]
  have hn : ∀ τ, 0 < ‖embS D τ γ‖ := fun τ => norm_embS_pos D hγ0 τ
  have habs : ∀ τ, |Cnt.Gz D (Tu D u) (Tu D u') Z τ| = ‖embS D τ γ‖ * s := fun τ => absGz_eq D F0 F' τ
  have hT0 : (0 : ℝ) ≤ ((Tu D u : ℕ) : ℝ) := Nat.cast_nonneg _
  have hT0' : (0 : ℝ) ≤ ((Tu D u' : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 : ∀ τ, max 1 (Cnt.Gz D (Tu D u) (Tu D u') Z τ)⁻¹ ≤ max 1 ‖embS D τ γ‖⁻¹ * s⁻¹ := by
    intro τ
    have hpos : 0 < |Cnt.Gz D (Tu D u) (Tu D u') Z τ| := by rw [habs]; exact mul_pos (hn τ) hs0
    have h2 : max 1 (Cnt.Gz D (Tu D u) (Tu D u') Z τ)⁻¹ ≤ max 1 |Cnt.Gz D (Tu D u) (Tu D u') Z τ|⁻¹ := by
      rcases le_or_gt (Cnt.Gz D (Tu D u) (Tu D u') Z τ) 0 with h | h
      · rw [max_eq_left (le_trans (inv_nonpos.2 h) zero_le_one)]; exact le_max_left _ _
      · rw [abs_of_pos h]
    refine le_trans h2 ?_
    rw [habs, mul_inv]
    refine le_trans (max_mul_le (inv_nonneg.2 (norm_nonneg _)) (inv_nonneg.2 hs0.le)) ?_
    rw [max_eq_right hsi]
  have h3 : ∀ τ, max 1 ‖embS D τ γ‖ ≤ max 1 |Cnt.Gz D (Tu D u) (Tu D u') Z τ| * s⁻¹ := by
    intro τ
    have e : ‖embS D τ γ‖ = |Cnt.Gz D (Tu D u) (Tu D u') Z τ| * s⁻¹ := by
      rw [habs, mul_assoc, mul_inv_cancel₀ hs0.ne', mul_one]
    rw [e]
    refine le_trans (max_mul_le (abs_nonneg _) (inv_nonneg.2 hs0.le)) ?_
    rw [max_eq_right hsi]
  have hG := prod_max_absGz_le D Z hb hC hβ hT0 hT hT0' hT' hr
  have hP0 : 0 ≤ ∏ τ, max 1 ‖embS D τ γ‖⁻¹ := Finset.prod_nonneg fun τ _ => le_trans zero_le_one (le_max_left _ _)
  calc ∏ τ, max 1 (Cnt.Gz D (Tu D u) (Tu D u') Z τ)⁻¹ ≤ ∏ τ, (max 1 ‖embS D τ γ‖⁻¹ * s⁻¹) :=
        Finset.prod_le_prod (fun τ _ => le_trans zero_le_one (le_max_left _ _)) (fun τ _ => h1 τ)
    _ = (∏ τ, max 1 ‖embS D τ γ‖⁻¹) * s⁻¹ ^ D.R.f := by rw [Finset.prod_mul_distrib, Finset.prod_const, hf]
    _ ≤ (∏ τ, max 1 ‖embS D τ γ‖) * s⁻¹ ^ D.R.f :=
        mul_le_mul_of_nonneg_right (prod_max_inv_le _ hn (one_le_prod_norm D γ hγ hγ0)) (by positivity)
    _ ≤ (∏ τ, (max 1 |Cnt.Gz D (Tu D u) (Tu D u') Z τ| * s⁻¹)) * s⁻¹ ^ D.R.f :=
        mul_le_mul_of_nonneg_right (Finset.prod_le_prod (fun τ _ => le_trans zero_le_one (le_max_left _ _))
          (fun τ _ => h3 τ)) (by positivity)
    _ = (∏ τ, max 1 |Cnt.Gz D (Tu D u) (Tu D u') Z τ|) * s⁻¹ ^ D.R.f * s⁻¹ ^ D.R.f := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, hf]
    _ ≤ Gbd D b C β Z * (R1 D ^ 2) ^ D.R.f * (R1 D ^ 2) ^ D.R.f := by
        have hsf : s⁻¹ ^ D.R.f ≤ (R1 D ^ 2) ^ D.R.f := pow_le_pow_left₀ (inv_nonneg.2 hs0.le) hsR _
        have hA : 0 ≤ ∏ τ, max 1 |Cnt.Gz D (Tu D u) (Tu D u') Z τ| :=
          Finset.prod_nonneg fun τ _ => le_trans zero_le_one (le_max_left _ _)
        have hsf0 : 0 ≤ s⁻¹ ^ D.R.f := by positivity
        calc (∏ τ, max 1 |Cnt.Gz D (Tu D u) (Tu D u') Z τ|) * s⁻¹ ^ D.R.f * s⁻¹ ^ D.R.f
            ≤ Gbd D b C β Z * (R1 D ^ 2) ^ D.R.f * s⁻¹ ^ D.R.f :=
              mul_le_mul_of_nonneg_right (mul_le_mul hG hsf hsf0 (le_trans hA hG)) hsf0
          _ ≤ Gbd D b C β Z * (R1 D ^ 2) ^ D.R.f * (R1 D ^ 2) ^ D.R.f :=
              mul_le_mul_of_nonneg_left hsf (by
                have : 0 ≤ Gbd D b C β Z := le_trans hA hG
                positivity)
    _ = _ := by ring

end Formalism.MainNotions.S.Pv.HH

end
