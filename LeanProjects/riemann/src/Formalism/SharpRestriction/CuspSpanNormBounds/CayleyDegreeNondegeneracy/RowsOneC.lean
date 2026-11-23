import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsND
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsOneN
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsOneA

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem weighted_sum_le_of_fibre_counts {Pr κ : Type} (S : Finset Pr) (w a₁ a₂ : Pr → ℝ) (c₁ c₂ : Pr → κ) (M R Φ : ℝ) (N : κ → κ → ℝ)
    (α₁ α₂ φ : κ → ℝ) (hM : 0 ≤ M) (hR : 0 ≤ R) (hw : ∀ p ∈ S, 0 ≤ w p) (ha₂ : ∀ p ∈ S, 0 ≤ a₂ p)
    (hα₁ : ∀ p ∈ S, a₁ p ≤ α₁ (c₁ p)) (hα₂ : ∀ p ∈ S, a₂ p ≤ α₂ (c₂ p))
    (hcount : ∀ x y, (∃ p ∈ S, c₁ p = x) → (∃ p ∈ S, c₂ p = y) → ∀ S' : Finset Pr, S' ⊆ S →
      (∀ p ∈ S', c₁ p = x ∧ c₂ p = y) → ∑ p ∈ S', w p ≤ M * N x y)
    (hN : ∀ x y, (∃ p ∈ S, c₁ p = x) → (∃ p ∈ S, c₂ p = y) → N x y * (α₁ x * α₂ y) ≤ R * (φ x * φ y))
    (hα0₁ : ∀ x, 0 ≤ α₁ x) (hα0₂ : ∀ x, 0 ≤ α₂ x) (hφ0 : ∀ x, 0 ≤ φ x)
    (hΦ₁ : ∀ 𝒵 : Finset κ, (∀ x ∈ 𝒵, ∃ p ∈ S, c₁ p = x) → ∑ x ∈ 𝒵, φ x ≤ Φ)
    (hΦ₂ : ∀ 𝒵 : Finset κ, (∀ x ∈ 𝒵, ∃ p ∈ S, c₂ p = x) → ∑ x ∈ 𝒵, φ x ≤ Φ) :
    ∑ p ∈ S, w p * (a₁ p * a₂ p) ≤ M * (R * Φ ^ 2) := by
  classical
  rw [rows_fibres S c₁ c₂]
  have h1 := hΦ₁ (S.image c₁) fun x hx => Finset.mem_image.1 hx
  have h2 := hΦ₂ (S.image c₂) fun x hx => Finset.mem_image.1 hx
  have hΦ0 : 0 ≤ Φ := le_trans (Finset.sum_nonneg fun x _ => hφ0 x) h1
  calc ∑ x ∈ S.image c₁, ∑ y ∈ S.image c₂, ∑ p ∈ S.filter (fun p => c₁ p = x ∧ c₂ p = y), w p * (a₁ p * a₂ p)
      ≤ ∑ x ∈ S.image c₁, ∑ y ∈ S.image c₂, M * (R * (φ x * φ y)) := by
        refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => ?_
        calc ∑ p ∈ S.filter (fun p => c₁ p = x ∧ c₂ p = y), w p * (a₁ p * a₂ p)
            ≤ ∑ p ∈ S.filter (fun p => c₁ p = x ∧ c₂ p = y), w p * (α₁ x * α₂ y) := by
              refine Finset.sum_le_sum fun p hp => ?_
              obtain ⟨hpS, e1, e2⟩ := Finset.mem_filter.1 hp
              refine mul_le_mul_of_nonneg_left ?_ (hw p hpS)
              exact mul_le_mul (e1 ▸ hα₁ p hpS) (e2 ▸ hα₂ p hpS) (ha₂ p hpS) (hα0₁ x)
          _ = (∑ p ∈ S.filter (fun p => c₁ p = x ∧ c₂ p = y), w p) * (α₁ x * α₂ y) := by rw [Finset.sum_mul]
          _ ≤ (M * N x y) * (α₁ x * α₂ y) :=
              mul_le_mul_of_nonneg_right (hcount x y (Finset.mem_image.1 hx) (Finset.mem_image.1 hy) _
                (Finset.filter_subset _ _) fun p hp => (Finset.mem_filter.1 hp).2) (mul_nonneg (hα0₁ x) (hα0₂ y))
          _ = M * (N x y * (α₁ x * α₂ y)) := by ring
          _ ≤ M * (R * (φ x * φ y)) :=
              mul_le_mul_of_nonneg_left (hN x y (Finset.mem_image.1 hx) (Finset.mem_image.1 hy)) hM
    _ = M * (R * ((∑ x ∈ S.image c₁, φ x) * ∑ y ∈ S.image c₂, φ y)) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ M * (R * Φ ^ 2) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hR) hM
        rw [sq]
        exact mul_le_mul h1 h2 (Finset.sum_nonneg fun x _ => hφ0 x) hΦ0

section One

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

def wordPairWeightRatio (D : D7) (u u' : D.what₂.Word) : ℝ :=
  4 * Real.sqrt (Tr D u' / Tr D u) * (gS D : ℝ) * gg D ^ (-(D.R.m : ℝ)) * ((D.R.k : ℝ) ^ D.R.rS)⁻¹

def smallTermBound (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C0 : ℝ) : ℝ :=
  2 * C0 * GamS D large₂ ^ 2 * (wordPairWeightRatio D u u' ^ D.R.f) ^ D.R.k

def logHeightExp (D : D7) (large₂ : SizeData₂ D) (C2 : ℝ) : ℝ := Real.exp (C2 * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b)

def smallTermLoss (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (c C2 Ch δ C0 : ℝ) (q : ℕ) (Z : GramM D) : ℝ :=
  (HHZ D large₂.sc.b c Z ^ (c * (D.R.rS : ℝ) ^ 2)) ^ 2 *
    (GamS D large₂ * sizeZ D large₂.sc.b Ch Z ^ (C2 * (D.R.m : ℝ) ^ 2)) *
    (logHeightExp D large₂ C2 * sizeZ D large₂.sc.b Ch Z ^ (C2 * (D.R.m : ℝ) ^ 4)) ^ 2 * ((1 + δ) * rDD D u') * smallTermBound D large₂ u u' C0 *
    sizeZ D large₂.sc.b Ch Z ^ (-(2 * (q : ℝ) / ((D.R.rS : ℝ) + 1)))

def smallTermAmplitude (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (c C2 Ch δ C0 : ℝ) (q : ℕ) (Z : GramM D) : ℝ :=
  Real.sqrt (smallTermLoss D large₂ u u' c C2 Ch δ C0 q Z / wordPairGramNorm D u u' Z)

def twoLabelCount (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (c : ℝ) (x y : GramM D) : ℝ :=
  min (wordPairSwapBound D large₂ u u' c x * gramPairQuadrupleBound D large₂ c x y) (wordPairSwapBound D large₂ u u' c y * gramPairQuadrupleBound D large₂ c y x)

def labelPairConstant (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (c C2 Ch δ C0 : ℝ) : ℝ :=
  c ^ D.R.f * ((rows_P D large₂ c Ch ^ (c * (D.R.rS : ℝ) ^ 2)) ^ 2 * (rows_P D large₂ c Ch ^ (c * (D.R.rS : ℝ) ^ 2)) ^ 2 *
    (rows_P D large₂ c Ch ^ (c * (D.R.rS : ℝ) ^ 2)) ^ 2) * GamS D large₂ * logHeightExp D large₂ C2 * ((1 + δ) * rDD D u') *
    Real.sqrt (smallTermBound D large₂ u u' C0)

def corankOneBound (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (c C2 Ch δ C0 : ℝ) : ℝ :=
  2 * (labelPairConstant D large₂ u u' c C2 Ch δ C0 * rows_Phi D large₂ c Ch ^ 2)

def IsSmallTerm (t : D.s.Term u u') : Prop :=
  Dr (X.fl t) (X.fl' t) ≠ 0 ∧ ∏ τ, min (nuV (Tr D u) (Y.W τ).z (Y.W τ).z' (Y.γ t τ)) (Tr D u') ≤
    (4 * Real.sqrt (Tr D u' / Tr D u) * (gS D : ℝ)) ^ D.R.f

variable {C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm : ℝ} {q : ℕ}

theorem one_le_rank_k (D : D7) : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega

theorem term_weight_pos (hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (h7 : VanishingOnXAndXPlus.adm7 D large₂ C' Cl Cg cb Cu cT CT C0)
    (τ : D.what₂.Tau) : 0 < tvPr D τ u' := by
  have hl := h7 hH0 u' τ
  have hg : 0 < gg D := by linarith [two_le_gg_of_count_hypotheses hH0]
  have hgm : 0 < gg D ^ (-(D.R.m : ℝ)) := Real.rpow_pos_of_pos hg _
  have hk0 : (0 : ℝ) < D.R.k := by exact_mod_cast one_le_rank_k D
  have hk : 0 < (D.R.k : ℝ) ^ (3 * D.R.rS) := by positivity
  have hT : 0 < Tcrit D u' τ := by
    by_contra hn
    have := mul_nonpos_of_nonneg_of_nonpos hgm.le (not_lt.1 hn)
    linarith
  unfold tvPr
  exact div_pos hT (rows_Tr_pos D u')

theorem prod_term_weight_pow_le (hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (h6 : VanishingOnXAndXPlus.adm6 D large₂ C' Cl Cg cb Cu cT CT C0 δ)
    (hδ2 : δ ≤ 1 / 2) : ∏ τ, tvPr D τ u' ^ D.R.k ≤ 2 * C0 * GamS D large₂ ^ 2 := by
  have h := abs_le.1 (h6 hH0 u')
  have hD := d_Dstar_pos D
  obtain ⟨_, _, _, _, _, _, _, _, _, h10, _⟩ := hH0.2.1
  have hC0 : 0 < C0 := lt_of_lt_of_le one_pos hH0.2.2
  have hΓ : 0 < GamS D large₂ := by unfold GamS; exact Real.exp_pos _
  have hw := (h10 u').1
  rw [d_GamP_eq D large₂ u'] at hw
  have e2 : GamS D large₂ ^ (-2 : ℤ) = (GamS D large₂ ^ 2)⁻¹ := by rw [zpow_neg]; norm_cast
  rw [e2] at hw
  have hd : 0 < (D.duS u' : ℝ) := lt_of_lt_of_le (by positivity) hw
  set P : ℝ := ∏ τ, (Tcrit D u' τ / Tr D u') ^ D.R.k with hP
  have e : ∏ τ, tvPr D τ u' ^ D.R.k = P := rfl
  rw [e]
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun τ _ => D.R.k_even.pow_nonneg _
  have h1 : P / 2 ≤ D.what₂.Dstar / (D.duS u' : ℝ) := by nlinarith [h.1]
  have h2 : D.what₂.Dstar / (D.duS u' : ℝ) ≤ C0 * GamS D large₂ ^ 2 := by
    rw [div_le_iff₀ hd]
    have a1 : (GamS D large₂ ^ 2)⁻¹ * D.what₂.Dstar ≤ (D.duS u' : ℝ) * C0 := (div_le_iff₀ hC0).1 hw
    have a2 : D.what₂.Dstar ≤ GamS D large₂ ^ 2 * ((D.duS u' : ℝ) * C0) := (inv_mul_le_iff₀ (by positivity)).1 a1
    linarith
  linarith

theorem weightRatio_nonneg (D : D7) (hg : 0 ≤ gg D) (u u' : D.what₂.Word) : 0 ≤ wordPairWeightRatio D u u' := by
  unfold wordPairWeightRatio; positivity

theorem smallTermBound_nonneg (D : D7) (large₂ : SizeData₂ D) (hg : 0 ≤ gg D) (u u' : D.what₂.Word) (hC0 : 0 ≤ C0) :
    0 ≤ smallTermBound D large₂ u u' C0 := by
  have := weightRatio_nonneg D hg u u'
  unfold smallTermBound; positivity

theorem ampMin_mono_constant (D : D7) {C C'' δ' : ℝ} (h0 : 0 ≤ C) (hCC : C ≤ C'') (hδ1 : δ' ≤ 1) (τ : D.what₂.Tau) (w w' : D.what₂.Word)
    (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (γ : MatKR D.R.k D.R.rS)
    (hx : 0 ≤ nuV (Tr D w) z z' γ * tvPr D τ w' * gg D ^ (-(D.R.m : ℝ))) :
    ampMinF D C δ' τ w w' z z' γ ≤ ampMinF D C'' δ' τ w w' z z' γ := by
  unfold ampMinF
  split_ifs
  · exact le_rfl
  · refine min_le_min le_rfl (mul_le_mul_of_nonneg_left ?_ hx)
    have ha : 0 ≤ 2 * (D.R.rS : ℝ) * (1 - δ') := by
      have : 0 ≤ 1 - δ' := by linarith
      positivity
    exact Real.rpow_le_rpow (by positivity) (by gcongr) ha

theorem small_term_pow_le (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q)
    (h7 : VanishingOnXAndXPlus.adm7 D large₂ C' Cl Cg cb Cu cT CT C0) (hδ2 : δ ≤ 1 / 2) (hδm0 : 0 ≤ δm) (hδm : δm ≤ 1 / 4) (hCa : 0 ≤ Ca)
    (hCak : (max Ca 1) ^ 3 ≤ D.R.k) (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0) (hrel : D.s.relevant t) (hsm : IsSmallTerm Y t) :
    rows_Mt Y Ca δm t ^ D.R.k ≤ smallTermBound D large₂ u u' C0 := by
  have hrd := d_rdE_pos h.hH.1
  have hg : 0 < gg D := by linarith [two_le_gg_of_count_hypotheses h.hH.1]
  have hk := one_le_rank_k D
  have hk0 : (0 : ℝ) < D.R.k := by exact_mod_cast hk
  have htv := fun τ => term_weight_pos (u' := u') h.hH.1 h7 τ
  have hC1 : (1 : ℝ) ≤ max Ca 1 := le_max_right _ _
  have m1 := rowsT_Mt_small Y hrd t hG hrel hsm.1 hC1 hδm0 (by linarith) hg hk (fun τ => h7 h.hH.1 u' τ) hsm.2 le_rfl
  have hgS : (0 : ℝ) ≤ (gS D : ℝ) := by positivity
  have m2 : (4 * Real.sqrt (Tr D u' / Tr D u) * (gS D : ℝ) * gg D ^ (-(D.R.m : ℝ)) *
      (max Ca 1 / D.R.k) ^ (2 * (D.R.rS : ℝ) * (1 - δm))) ^ D.R.f ≤ wordPairWeightRatio D u u' ^ D.R.f := by
    apply pow_le_pow_left₀ (by positivity)
    unfold wordPairWeightRatio
    exact mul_le_mul_of_nonneg_left (div_rpow_le_inv_pow hk hC1 hδm hCak) (by positivity)
  have hP0 : 0 ≤ ∏ τ, tvPr D τ u' := Finset.prod_nonneg fun τ _ => (htv τ).le
  have hx : ∀ τ, 0 ≤ nuV (Tr D u) (Y.W τ).z (Y.W τ).z' (Y.γ t τ) * tvPr D τ u' * gg D ^ (-(D.R.m : ℝ)) := by
    intro τ
    have hν : 0 ≤ nuV (Tr D u) (Y.W τ).z (Y.W τ).z' (Y.γ t τ) := by
      unfold nuV
      rw [d_Gf_eq Y hrd t τ]
      exact div_nonneg (rows_Gz_pos Y h.hT hrd t hG hrel τ).le (mul_nonneg (rows_Tr_pos D u).le (sq_nonneg _))
    have := (htv τ).le
    positivity
  have a0 : ∀ τ, 0 ≤ ampMinF D Ca δm τ u u' (Y.W τ).z (Y.W τ).z' (Y.γ t τ) := by
    intro τ
    unfold ampMinF
    split_ifs
    · exact zero_le_one
    · exact le_min zero_le_one (mul_nonneg (hx τ) (Real.rpow_nonneg (by positivity) _))
  have m0 : 0 ≤ rows_Mt Y Ca δm t := by
    unfold rows_Mt; exact Finset.prod_nonneg fun τ _ => a0 τ
  have mm : rows_Mt Y Ca δm t ≤ rows_Mt Y (max Ca 1) δm t := by
    unfold rows_Mt
    exact Finset.prod_le_prod (fun τ _ => a0 τ) fun τ _ =>
      ampMin_mono_constant D hCa (le_max_left _ _) (by linarith) τ u u' _ _ _ (hx τ)
  have m3 : rows_Mt Y Ca δm t ≤ (∏ τ, tvPr D τ u') * wordPairWeightRatio D u u' ^ D.R.f :=
    mm.trans (m1.trans (mul_le_mul_of_nonneg_left m2 hP0))
  calc rows_Mt Y Ca δm t ^ D.R.k ≤ ((∏ τ, tvPr D τ u') * wordPairWeightRatio D u u' ^ D.R.f) ^ D.R.k := pow_le_pow_left₀ m0 m3 _
    _ = (∏ τ, tvPr D τ u' ^ D.R.k) * (wordPairWeightRatio D u u' ^ D.R.f) ^ D.R.k := by rw [mul_pow, Finset.prod_pow]
    _ ≤ 2 * C0 * GamS D large₂ ^ 2 * (wordPairWeightRatio D u u' ^ D.R.f) ^ D.R.k :=
        mul_le_mul_of_nonneg_right (prod_term_weight_pow_le h.hH.1 h.h6 hδ2) (by have := weightRatio_nonneg D hg.le u u'; positivity)

theorem small_term_amplitude_le (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q)
    (h7 : VanishingOnXAndXPlus.adm7 D large₂ C' Cl Cg cb Cu cT CT C0) (hδ2 : δ ≤ 1 / 2) (hδm0 : 0 ≤ δm) (hδm : δm ≤ 1 / 4) (hCa : 0 ≤ Ca)
    (hCak : (max Ca 1) ^ 3 ≤ D.R.k) (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0) (hrel : D.s.relevant t) (hsm : IsSmallTerm Y t) :
    aT X t / Real.sqrt (dimPi (hc := D.hcW) u) ≤ smallTermAmplitude D large₂ u u' c C2 Ch δ C0 q (termReducedGramMatrix Y h.hH h.hHH t) := by
  obtain ⟨hEq, hGood⟩ := rows_Zr_spec Y h.hH h.hHH t hG hrel
  have h1 := rows_term_MINIdec Y h.hH h.hDEC h.ha h.hb h.hp h.hpp h.h6 h.hδ h.hV h.hT h.hCh t hG hrel q h.hq
  have hM := small_term_pow_le Y h h7 hδ2 hδm0 hδm hCa hCak t hG hrel hsm
  rw [← rows_nZ_inv hEq, ← rows_HHZ_inv hEq, ← rows_sizeZ_inv hEq] at h1
  have hσ := rows_one_le_sizeZ (D := D) large₂.sc.b Ch (termReducedGramMatrix Y h.hH h.hHH t)
  have hHH1 := rows_one_le_HHZ D large₂ h.hc (termReducedGramMatrix Y h.hH h.hHH t)
  have hΓ : 0 < GamS D large₂ := by unfold GamS; exact Real.exp_pos _
  have hτ0 : 0 ≤ (1 + δ) * rDD D u' := mul_nonneg (by linarith [h.hδ]) (rows_rDD_nonneg D u')
  have h1' : wordPairGramNorm D u u' (termReducedGramMatrix Y h.hH h.hHH t) * aT X t ^ 2 / dimPi (hc := D.hcW) u ≤
      smallTermLoss D large₂ u u' c C2 Ch δ C0 q (termReducedGramMatrix Y h.hH h.hHH t) := by
    refine h1.trans ?_
    unfold smallTermLoss logHeightExp
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM ?_) (by positivity)
    positivity
  have h2 : aT X t ^ 2 / dimPi (hc := D.hcW) u ≤ smallTermLoss D large₂ u u' c C2 Ch δ C0 q (termReducedGramMatrix Y h.hH h.hHH t) /
      wordPairGramNorm D u u' (termReducedGramMatrix Y h.hH h.hHH t) := by
    rw [le_div_iff₀ (rows_nZ_pos Y h hGood)]
    calc aT X t ^ 2 / dimPi (hc := D.hcW) u * wordPairGramNorm D u u' (termReducedGramMatrix Y h.hH h.hHH t)
        = wordPairGramNorm D u u' (termReducedGramMatrix Y h.hH h.hHH t) * aT X t ^ 2 / dimPi (hc := D.hcW) u := by ring
      _ ≤ _ := h1'
  have h3 : aT X t / Real.sqrt (dimPi (hc := D.hcW) u) = Real.sqrt (aT X t ^ 2 / dimPi (hc := D.hcW) u) := by
    rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (aT_nonneg X t)]
  rw [h3]
  exact Real.sqrt_le_sqrt h2

end One

end Formalism.MainNotions.BridgeLemma₂

end
