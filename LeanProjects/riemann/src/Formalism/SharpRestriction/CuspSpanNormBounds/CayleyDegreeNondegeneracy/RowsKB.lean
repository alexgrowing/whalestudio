import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsDegF

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section KB

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

theorem rows_HHZ_eq (D : D7) (large₂ : SizeData₂ D) (c : ℝ) (Z : GramM D) :
    HHZ D large₂.sc.b c Z = large₂.sc.b ^ (c ^ 2 * (D.R.m : ℝ) ^ 3 * D.R.f) * sizeZ D large₂.sc.b c Z ^ 4 := by
  have hb0 : 0 < large₂.sc.b := by linarith [d_two_le_b D large₂]
  unfold HHZ
  rw [← Real.rpow_mul hb0.le]
  congr 2
  ring

theorem rows_bpow_le_HHZ (D : D7) (large₂ : SizeData₂ D) {c E : ℝ} (hE : E ≤ c ^ 2 * (D.R.m : ℝ) ^ 3 * D.R.f) (Z : GramM D) :
    large₂.sc.b ^ E ≤ HHZ D large₂.sc.b c Z := by
  have hb := d_two_le_b D large₂
  rw [rows_HHZ_eq]
  have h2 : 1 ≤ sizeZ D large₂.sc.b c Z ^ 4 := one_le_pow₀ (rows_one_le_sizeZ _ _ _)
  calc large₂.sc.b ^ E ≤ large₂.sc.b ^ (c ^ 2 * (D.R.m : ℝ) ^ 3 * D.R.f) := Real.rpow_le_rpow_of_exponent_le (by linarith) hE
    _ = large₂.sc.b ^ (c ^ 2 * (D.R.m : ℝ) ^ 3 * D.R.f) * 1 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)

theorem rows_Dr_le_HHZ (D : D7) (large₂ : SizeData₂ D) (hrd : 0 < D.host.rdE) (hr : 1 ≤ D.R.rS) {c : ℝ} (hc1 : 1 ≤ c) (Z : GramM D) :
    ∏ τ, max 1 (absDl D Z D.R.rS τ ^ 2) ≤ HHZ D large₂.sc.b c Z := by
  have hb := d_two_le_b D large₂
  have hb0 : 0 < large₂.sc.b := by linarith
  set H2 : ℝ := large₂.sc.b ^ (c * (D.R.m : ℝ) ^ 2) with hH2
  have hH21 : 1 ≤ H2 := Real.one_le_rpow (by linarith) (by positivity)
  have hm2 : (2 : ℝ) ≤ D.R.m := by
    rw [rows_m_cast]; have : (0 : ℝ) ≤ D.R.rS := by positivity
    linarith
  have each : ∀ τ, max 1 (absDl D Z D.R.rS τ ^ 2) ≤ (H2 * max 1 (absDl D Z D.R.rS τ / H2)) ^ 2 := by
    intro τ
    have hD0 := rows_absDl_nonneg hrd Z D.R.rS τ
    have a1 : 1 ≤ H2 * max 1 (absDl D Z D.R.rS τ / H2) := one_le_mul_of_one_le_of_one_le hH21 (le_max_left _ _)
    have a2 : absDl D Z D.R.rS τ ≤ H2 * max 1 (absDl D Z D.R.rS τ / H2) := by
      calc absDl D Z D.R.rS τ = H2 * (absDl D Z D.R.rS τ / H2) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)
    exact max_le (one_le_pow₀ a1) (pow_le_pow_left₀ hD0 a2 2)
  have single : ∀ τ, max 1 (absDl D Z D.R.rS τ / H2) ≤
      ∏ l ∈ Finset.Icc 1 (D.R.rS + 1), max 1 (absDl D Z l τ / H2) := by
    intro τ
    have hmem : D.R.rS ∈ Finset.Icc 1 (D.R.rS + 1) := Finset.mem_Icc.2 ⟨hr, Nat.le_succ _⟩
    rw [← Finset.mul_prod_erase _ _ hmem]
    exact le_mul_of_one_le_right (le_trans zero_le_one (le_max_left _ _))
      (rows_one_le_prod _ _ fun l _ => le_max_left _ _)
  have hs1 := rows_one_le_sizeZ (D := D) large₂.sc.b c Z
  calc ∏ τ, max 1 (absDl D Z D.R.rS τ ^ 2)
      ≤ ∏ τ : D.what₂.Tau, (H2 * max 1 (absDl D Z D.R.rS τ / H2)) ^ 2 :=
        Finset.prod_le_prod (fun τ _ => le_trans zero_le_one (le_max_left _ _)) fun τ _ => each τ
    _ = (H2 ^ D.R.f * ∏ τ : D.what₂.Tau, max 1 (absDl D Z D.R.rS τ / H2)) ^ 2 := by
        rw [Finset.prod_pow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, D.what₂.card_Tau]
    _ ≤ (H2 ^ D.R.f * sizeZ D large₂.sc.b c Z) ^ 2 := by
        apply pow_le_pow_left₀ (mul_nonneg (by positivity)
          (Finset.prod_nonneg fun τ _ => le_trans zero_le_one (le_max_left _ _)))
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        unfold sizeZ
        exact Finset.prod_le_prod (fun τ _ => le_trans zero_le_one (le_max_left _ _)) fun τ _ => single τ
    _ = (H2 ^ D.R.f) ^ 2 * sizeZ D large₂.sc.b c Z ^ 2 := by ring
    _ ≤ large₂.sc.b ^ (c ^ 2 * (D.R.m : ℝ) ^ 3 * D.R.f) * sizeZ D large₂.sc.b c Z ^ 4 := by
        apply mul_le_mul _ (pow_le_pow_right₀ hs1 (by norm_num)) (by positivity) (by positivity)
        rw [hH2, rows_rpow_pow hb0, rows_rpow_pow hb0]
        apply Real.rpow_le_rpow_of_exponent_le (by linarith)
        push_cast
        have h0 : 0 ≤ c * (D.R.m : ℝ) ^ 2 * D.R.f := by positivity
        have h1 : (2 : ℝ) ≤ c * D.R.m := by nlinarith
        calc c * (D.R.m : ℝ) ^ 2 * D.R.f * 2 = (c * (D.R.m : ℝ) ^ 2 * D.R.f) * 2 := by ring
          _ ≤ (c * (D.R.m : ℝ) ^ 2 * D.R.f) * (c * D.R.m) := mul_le_mul_of_nonneg_left h1 h0
          _ = _ := by ring
    _ = _ := (rows_HHZ_eq D large₂ c Z).symm

theorem rows_KBound_of {C' Cl Cg cb Cu cT CT C0 A c : ℝ} (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hHH : UnitaryVolumeMass.stHH D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c) (hc1 : 1 ≤ c) (hCT : CT ≤ c) : rows_KBound Y c := by
  intro t hG hrel
  have hrd := d_rdE_pos hH.1
  have hb := d_two_le_b D large₂
  have hb0 : 0 < large₂.sc.b := by linarith
  have hHH1 := rows_one_le_HHZ D large₂ (by linarith : 0 ≤ c) (termGramMatrix X t)
  by_cases hD : Dr (X.fl t) (X.fl' t) = 0
  · have e : rows_Kt Y t = 1 := by
      unfold rows_Kt
      refine Finset.prod_eq_one fun τ _ => ?_
      unfold chRatio
      rw [if_pos ((rows_Dr_zero_iff Y hrd t τ).2 hD)]
    rw [e, one_pow]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ hHH1)
  · have eK : rows_Kt Y t = ∏ τ, (1 + Lat.ch (Tu D u) (Tu D u') (X.fl t) (X.fl' t) (embS D τ)) /
        Lat.sh (Tu D u) (Tu D u') (X.fl t) (X.fl' t) (embS D τ) := by
      unfold rows_Kt
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [rows_chRatio_eq Y hrd t τ]
      unfold onePlusChSh
      rw [if_neg hD]
    have hT1 : 1 ≤ Tr D u := by unfold Tr; exact_mod_cast (D.mem u).A.T_prime.pos
    have hT1' : 1 ≤ Tr D u' := by unfold Tr; exact_mod_cast (D.mem u').A.T_prime.pos
    have hDpos : ∀ τ, 0 < absDl D (termGramMatrix X t) D.R.rS τ := by
      intro τ
      rw [← d_norm_Dmin Y hrd t τ D.R.rS (Nat.le_succ _)]
      exact norm_pos_iff.2 fun h => hD ((rows_Dr_zero_iff Y hrd t τ).1 h)
    have hGeq : ∀ τ, Gz D (Tu D u) (Tu D u') (termGramMatrix X t) τ = Tr D u * Tr D u' * absDl D (termGramMatrix X t) D.R.rS τ ^ 2 *
        Lat.sh (Tu D u) (Tu D u') (X.fl t) (X.fl' t) (embS D τ) ^ 2 := by
      intro τ
      have h := rowsT_nu_eq Y hrd t hG hrel hD τ
      unfold nuV at h
      rw [d_Gf_eq Y hrd t τ, d_norm_Dmin Y hrd t τ D.R.rS (Nat.le_succ _)] at h
      have hne : Tr D u * absDl D (termGramMatrix X t) D.R.rS τ ^ 2 ≠ 0 := by
        have := hDpos τ
        positivity
      rw [div_eq_iff hne] at h
      rw [h]; ring
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h23, _, _⟩ := hH.1.1
    have hm2 : (2 : ℝ) ≤ D.R.m := by
      rw [rows_m_cast]; have : (0 : ℝ) ≤ D.R.rS := by positivity
      linarith
    have h6 : (Tr D u * Tr D u') ^ Fintype.card D.what₂.Tau ≤ HHZ D large₂.sc.b c (termGramMatrix X t) := by
      rw [D.what₂.card_Tau]
      have a1 : Tr D u * Tr D u' ≤ large₂.sc.b ^ (2 * (c * D.R.m)) := by
        have b1 : Tr D u ≤ large₂.sc.b ^ (c * (D.R.m : ℝ)) := (h23 u).2.trans
          (Real.rpow_le_rpow_of_exponent_le (by linarith) (by gcongr))
        have b2 : Tr D u' ≤ large₂.sc.b ^ (c * (D.R.m : ℝ)) := (h23 u').2.trans
          (Real.rpow_le_rpow_of_exponent_le (by linarith) (by gcongr))
        calc Tr D u * Tr D u' ≤ large₂.sc.b ^ (c * (D.R.m : ℝ)) * large₂.sc.b ^ (c * (D.R.m : ℝ)) :=
              mul_le_mul b1 b2 (by linarith) (by positivity)
          _ = _ := by rw [← Real.rpow_add hb0]; congr 1; ring
      calc (Tr D u * Tr D u') ^ D.R.f ≤ (large₂.sc.b ^ (2 * (c * D.R.m))) ^ D.R.f :=
            pow_le_pow_left₀ (by positivity) a1 _
        _ = large₂.sc.b ^ (2 * (c * D.R.m) * D.R.f) := rows_rpow_pow hb0 _ _
        _ ≤ _ := rows_bpow_le_HHZ D large₂ (by
            have h0 : 0 ≤ c * (D.R.m : ℝ) * D.R.f := by positivity
            have h1 : (2 : ℝ) ≤ c * (D.R.m : ℝ) ^ 2 := by nlinarith
            calc 2 * (c * (D.R.m : ℝ)) * D.R.f = (c * (D.R.m : ℝ) * D.R.f) * 2 := by ring
              _ ≤ (c * (D.R.m : ℝ) * D.R.f) * (c * (D.R.m : ℝ) ^ 2) := mul_le_mul_of_nonneg_left h1 h0
              _ = _ := by ring) _
    have h8 : ∏ τ, max 1 (1 / Gz D (Tu D u) (Tu D u') (termGramMatrix X t) τ) ≤ HHZ D large₂.sc.b c (termGramMatrix X t) := by
      simp only [one_div]
      exact (rowsT_HH_term Y hH hHH t hG hrel).2.2.1
    have key := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.degFactorBound D.what₂.Tau
      (fun τ => Lat.sh (Tu D u) (Tu D u') (X.fl t) (X.fl' t) (embS D τ))
      (fun τ => Lat.ch (Tu D u) (Tu D u') (X.fl t) (X.fl' t) (embS D τ))
      (fun τ => Gz D (Tu D u) (Tu D u') (termGramMatrix X t) τ) (fun τ => absDl D (termGramMatrix X t) D.R.rS τ)
      (Tr D u) (Tr D u') (HHZ D large₂.sc.b c (termGramMatrix X t)) (one_le_mul_of_one_le_of_one_le hT1 hT1')
      (fun τ => ⟨rowsT_sh_pos Y hrd t hG hrel hD τ, by
        unfold Lat.ch; exact div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _), rowsT_ch_sq Y hrd t hG hrel hD τ⟩)
      (fun τ => rowsT_Gz_pos Y hrd t hG hrel τ) hDpos hGeq h6
      (rows_Dr_le_HHZ D large₂ hrd hH.2.1.1 hc1 _) h8
    rw [D.what₂.card_Tau] at key
    rw [eK]
    exact key

end KB

section Fam

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1)

theorem rows_KBoundF_of (hAdm : VanishingOnXAndXPlus.AdmF Fm C1 X Y) : rows_KBoundF Fm C1 X Y := by
  intro Cg cb Cu cT CT C0 A
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hall⟩ := hAdm
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h27, _⟩ := hall Cg cb Cu cT CT C0 A
  obtain ⟨cH, x27, H27⟩ := h27
  refine ⟨max (max 1 CT) (|cH| + 2), fun c hc => ⟨x27, fun x hx i hx1 u u' hH => ?_⟩⟩
  have k1 : 1 ≤ c := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hc
  have k2 : CT ≤ c := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hc
  have k3 : |cH| + 2 ≤ c := le_trans (le_max_right _ _) hc
  exact rows_KBound_of _ hH
    (rows_stHH_mono (by linarith [le_abs_self cH]) (by linarith [neg_abs_le cH]) (H27 x hx i u u')) k1 k2

theorem rows_DegF_of' (hAdm : VanishingOnXAndXPlus.AdmF Fm C1 X Y) (hAmp : rows_AmpF Fm C1) (hT : rows_TiesF Fm C1 X Y) :
    rows_DegF Fm C1 X Y := rows_DegF_of Fm C1 X Y hAdm hAmp hT (rows_KBoundF_of Fm C1 X Y hAdm)

end Fam

end Formalism.MainNotions.BridgeLemma₂

end
