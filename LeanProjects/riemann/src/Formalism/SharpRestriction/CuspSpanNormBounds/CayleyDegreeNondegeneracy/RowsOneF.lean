import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsOneE
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsNDF

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem decay_length_sufficient {m k r c B : ℝ} (hm : m = 2 * r + 2) (hr : 0 ≤ r) (hk : m + 3 ≤ k) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (ha : B * m ^ 5 ≤ k) :
    (r + 1) * (12 * (c * r ^ 2) + B * m ^ 2 / 2 + B * m ^ 4 + 12 * (r + 1) ^ 2) + 1 ≤ (9 * c + 3) * k * m ^ 2 := by
  have hm2 : 2 ≤ m := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hk0 : 0 ≤ k := by linarith
  have hr1 : r + 1 = m / 2 := by linarith
  have e : (r + 1) * (12 * (c * r ^ 2) + B * m ^ 2 / 2 + B * m ^ 4 + 12 * (r + 1) ^ 2) + 1 =
      6 * m * (c * r ^ 2) + (B * m ^ 3) / 4 + (B * m ^ 5) / 2 + (m / 2) * (12 * (m / 2) ^ 2) + 1 := by rw [hr1]; ring
  have p1 : 6 * m * (c * r ^ 2) ≤ 2 * (c * k * m ^ 2) := by
    have a : r ^ 2 ≤ m ^ 2 / 4 := by nlinarith
    have b : c * r ^ 2 ≤ c * (m ^ 2 / 4) := mul_le_mul_of_nonneg_left a hc
    have d : 6 * m * (c * r ^ 2) ≤ 6 * m * (c * (m ^ 2 / 4)) := mul_le_mul_of_nonneg_left b (by linarith)
    nlinarith [mul_nonneg (mul_nonneg hc (sq_nonneg m)) (by linarith : 0 ≤ k - m)]
  have m35 : m ^ 3 ≤ m ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have p2 : B * m ^ 3 ≤ k := le_trans (mul_le_mul_of_nonneg_left m35 hB) ha
  have p4 : (m / 2) * (12 * (m / 2) ^ 2) ≤ (3 / 2) * (k * m ^ 2) := by
    nlinarith [mul_nonneg (sq_nonneg m) (by linarith : 0 ≤ k - m)]
  have p5 : (1 : ℝ) ≤ (1 / 2) * (k * m ^ 2) := by nlinarith
  have hm4 : 4 ≤ m ^ 2 := by nlinarith
  have p6 : k ≤ (1 / 4) * (k * m ^ 2) := by nlinarith [mul_nonneg hk0 (sub_nonneg.2 hm4)]
  have hU : 0 ≤ c * k * m ^ 2 := by positivity
  rw [e]
  have t : (9 * c + 3) * k * m ^ 2 = 9 * (c * k * m ^ 2) + 3 * (k * m ^ 2) := by ring
  rw [t]
  linarith

theorem le_max_four (a b c d : ℝ) : a ≤ max (max a b) (max c d) ∧ b ≤ max (max a b) (max c d) ∧
    c ≤ max (max a b) (max c d) ∧ d ≤ max (max a b) (max c d) :=
  ⟨le_trans (le_max_left _ _) (le_max_left _ _), le_trans (le_max_right _ _) (le_max_left _ _),
    le_trans (le_max_left _ _) (le_max_right _ _), le_trans (le_max_right _ _) (le_max_right _ _)⟩

section Mono

variable {D : D7} {large₂ : SizeData₂ D} {u u' : D.what₂.Word}

theorem height_pow_mono_constant (large₂ : SizeData₂ D) (hrd : 0 < D.host.rdE) {c' c : ℝ} (h : |c'| + 2 ≤ c) (Z : GramM D) :
    HHZ D large₂.sc.b c' Z ^ (c' * (D.R.rS : ℝ) ^ 2) ≤ HHZ D large₂.sc.b c Z ^ (c * (D.R.rS : ℝ) ^ 2) := by
  have h1 : c' ≤ c := by linarith [le_abs_self c']
  have h2 : 2 ≤ c + c' := by linarith [neg_abs_le c']
  have mono := rows_HHZ_mono large₂ hrd h1 h2 Z
  have o := rows_one_le_HHZ' D large₂ c' Z
  have hc : 0 ≤ c := by linarith [abs_nonneg c']
  calc HHZ D large₂.sc.b c' Z ^ (c' * (D.R.rS : ℝ) ^ 2) ≤ HHZ D large₂.sc.b c' Z ^ (c * (D.R.rS : ℝ) ^ 2) :=
        Real.rpow_le_rpow_of_exponent_le o (by gcongr)
    _ ≤ HHZ D large₂.sc.b c Z ^ (c * (D.R.rS : ℝ) ^ 2) := Real.rpow_le_rpow (by linarith) mono (by positivity)

theorem switch_bound_mono_constant {C' Cl Cg cb Cu cT CT C0 A c' c : ℝ} (h1 : |c'| + 2 ≤ c)
    (h : UnitaryVolumeMass.stSW D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c') : UnitaryVolumeMass.stSW D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c := by
  intro hH F0 he hz what₂ hrows Z hZ
  have h0 := h hH F0 he hz what₂ hrows Z hZ
  unfold MeanLe at h0 ⊢
  have hB : HHZ D large₂.sc.b c' Z ^ (c' * (D.R.rS : ℝ) ^ 2) * ∏ τ, nV D (Tu D u) (Tu D u') Z τ ≤
      HHZ D large₂.sc.b c Z ^ (c * (D.R.rS : ℝ) ^ 2) * ∏ τ, nV D (Tu D u) (Tu D u') Z τ := by
    refine mul_le_mul_of_nonneg_right (height_pow_mono_constant large₂ (d_rdE_pos hH.1) h1 Z) ?_
    refine Finset.prod_nonneg fun τ _ => ?_
    unfold nV
    exact D.R.k_even.pow_nonneg _
  exact h0.trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hB))

theorem partner_count_bound_mono_constant {C' Cl Cg cb Cu cT CT C0 A c' c : ℝ} (h1 : |c'| + 2 ≤ c)
    (h : UnitaryVolumeMass.PartnerCountBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c') : UnitaryVolumeMass.PartnerCountBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c := by
  intro hH F0 he hz Λ hΛ F' hF' hgen hR Z hZ
  refine (h hH F0 he hz Λ hΛ F' hF' hgen hR Z hZ).trans (ENNReal.ofReal_le_ofReal ?_)
  have hrd := d_rdE_pos hH.1
  have k1 : c' ≤ c := by linarith [le_abs_self c']
  have k2 : 2 ≤ c + c' := by linarith [neg_abs_le c']
  have hc : 0 ≤ c := by linarith [abs_nonneg c']
  have ma := rows_HHZ_mono large₂ hrd k1 k2 (ZhatL (lf D F0) F')
  have mb := rows_HHZ_mono large₂ hrd k1 k2 Z
  have oa := rows_one_le_HHZ' D large₂ c' (ZhatL (lf D F0) F')
  have ob := rows_one_le_HHZ' D large₂ c' Z
  have o : 1 ≤ HHZ D large₂.sc.b c' (ZhatL (lf D F0) F') * HHZ D large₂.sc.b c' Z := one_le_mul_of_one_le_of_one_le oa ob
  have hp : c' ^ D.R.f ≤ c ^ D.R.f :=
    (le_abs_self _).trans (by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) _)
  refine mul_le_mul hp ?_ (Real.rpow_nonneg (by linarith) _) (pow_nonneg hc _)
  calc (HHZ D large₂.sc.b c' (ZhatL (lf D F0) F') * HHZ D large₂.sc.b c' Z) ^ (c' * (D.R.rS : ℝ) ^ 2)
      ≤ (HHZ D large₂.sc.b c' (ZhatL (lf D F0) F') * HHZ D large₂.sc.b c' Z) ^ (c * (D.R.rS : ℝ) ^ 2) :=
        Real.rpow_le_rpow_of_exponent_le o (by gcongr)
    _ ≤ _ := Real.rpow_le_rpow (by linarith) (mul_le_mul ma mb (by linarith) (by linarith)) (by positivity)

end Mono

section Fam

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1)

def FamilyAmplitudeBounds : Prop :=
  ∀ Cg cb Cu cT CT C0 A Cpr : ℝ, ∃ C C2 Ch : ℝ, 0 ≤ Ch ∧ 0 ≤ C ∧ ∀ δ > 0, OwnEv Fm fun C' Cl x i =>
    VanishingOnXAndXPlus.AmplitudeBoundsConjunction (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1 Cpr C C2 Ch δ

theorem amplitude_bounds_of_family_amplitude_bounds (h : FamilyAmplitudeBounds Fm C1) : rows_AmpF Fm C1 := by
  intro Cg cb Cu cT CT C0 A Cpr
  obtain ⟨C, C2, Ch, h1, _, h3⟩ := h Cg cb Cu cT CT C0 A Cpr
  exact ⟨C, C2, Ch, h1, h3⟩

theorem rows_OneF_of (hAdm : VanishingOnXAndXPlus.AdmF Fm C1 X Y) (hAmp : FamilyAmplitudeBounds Fm C1) (hT : rows_TiesF Fm C1 X Y)
    (hTI : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), wordPairTermInjective (X x hx i) (Y x hx i u u'))
    (hBL : ∀ x (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), wordPairBetaLattice (Fm.D x i) u u') :
    rows_OneF Fm C1 X Y := by
  intro Cg cb Cu cT CT C0 A
  obtain ⟨_, _, _, _, _, _, _, h10a, _, _, _, h14, _, _, _, _, hall⟩ := hAdm
  obtain ⟨_, _, _, _, _, _, _, h4, h6, h7, h8, _, h10b, _, _, h20, h21, _, h27, hVol⟩ := hall Cg cb Cu cT CT C0 A
  obtain ⟨c3, LocalHeightDeterminant⟩ := h20 3
  obtain ⟨cH, x27, H27⟩ := h27
  obtain ⟨cV, xV, HV⟩ := hVol
  obtain ⟨cS, x4, H4⟩ := h4
  obtain ⟨c4, x21, H21⟩ := h21
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = max (max c3 1) (max (max (|cH| + 2) (|cV| + 2)) (max (|cS| + 2) (|c4| + 2))) := ⟨_, rfl⟩
  have k1 : c3 ≤ c := by rw [hcdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have k2 : 1 ≤ c := by rw [hcdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have k3 : |cH| + 2 ≤ c := by rw [hcdef]; exact le_trans (le_max_four _ _ _ _).1 (le_max_right _ _)
  have k4 : |cV| + 2 ≤ c := by rw [hcdef]; exact le_trans (le_max_four _ _ _ _).2.1 (le_max_right _ _)
  have k5 : |cS| + 2 ≤ c := by rw [hcdef]; exact le_trans (le_max_four _ _ _ _).2.2.1 (le_max_right _ _)
  have k6 : |c4| + 2 ≤ c := by rw [hcdef]; exact le_trans (le_max_four _ _ _ _).2.2.2 (le_max_right _ _)
  obtain ⟨x20, H20x⟩ := LocalHeightDeterminant c k1
  obtain ⟨Ca, C2, Ch, hCh, hCa, HA⟩ := hAmp Cg cb Cu cT CT C0 A (9 * c + 3)
  obtain ⟨xA, HAx⟩ := HA (1 / 4) (by norm_num)
  obtain ⟨x6, H6⟩ := h6 (1 / 2) (by norm_num)
  obtain ⟨x7, H7⟩ := h7
  obtain ⟨x8, H8⟩ := h8
  obtain ⟨x10, H10⟩ := h10b
  obtain ⟨xk, _, Hk⟩ := ev_kLow Fm |C2|
  obtain ⟨xc, _, Hc⟩ := ev_k Fm ((max Ca 1) ^ 3)
  refine ⟨max (max (4 * Real.sqrt A) (2 * Real.sqrt (2 * C0) * c))
    (max (Fm.CGam + C2) (4 + 2 * (c ^ 2 + 2 * max (Ch - c) 0) * (c + 1))), fun C hC => ?_⟩
  refine ownEv_intro Fm (max (max (max (max x20 x27) (max xV xA)) (max (max x6 x8) (max x10 xk)))
    (max (max x4 x21) (max x7 xc))) fun x hx _ i hx1 u u' hH => ?_
  have hM1 : max (max x20 x27) (max xV xA) ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hM2 : max (max x6 x8) (max x10 xk) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hM3 : max (max x4 x21) (max x7 xc) ≤ x := le_trans (le_max_right _ _) hx
  have g20 : x20 ≤ x := le_trans (le_max_four _ _ _ _).1 hM1
  have g27 : x27 ≤ x := le_trans (le_max_four _ _ _ _).2.1 hM1
  have gV : xV ≤ x := le_trans (le_max_four _ _ _ _).2.2.1 hM1
  have gA : xA ≤ x := le_trans (le_max_four _ _ _ _).2.2.2 hM1
  have g6 : x6 ≤ x := le_trans (le_max_four _ _ _ _).1 hM2
  have g8 : x8 ≤ x := le_trans (le_max_four _ _ _ _).2.1 hM2
  have g10 : x10 ≤ x := le_trans (le_max_four _ _ _ _).2.2.1 hM2
  have gk : xk ≤ x := le_trans (le_max_four _ _ _ _).2.2.2 hM2
  have g4 : x4 ≤ x := le_trans (le_max_four _ _ _ _).1 hM3
  have g21 : x21 ≤ x := le_trans (le_max_four _ _ _ _).2.1 hM3
  have g7 : x7 ≤ x := le_trans (le_max_four _ _ _ _).2.2.1 hM3
  have gc : xc ≤ x := le_trans (le_max_four _ _ _ _).2.2.2 hM3
  have hc0 : 0 ≤ c := by linarith
  have q1 : 4 * Real.sqrt A ≤ C := le_trans (le_max_four _ _ _ _).1 hC
  have q2 : 2 * Real.sqrt (2 * C0) * c ≤ C := le_trans (le_max_four _ _ _ _).2.1 hC
  have q3 : Fm.CGam + C2 ≤ C := le_trans (le_max_four _ _ _ _).2.2.1 hC
  have q4 : 4 + 2 * (c ^ 2 + 2 * max (Ch - c) 0) * (c + 1) ≤ C := le_trans (le_max_four _ _ _ _).2.2.2 hC
  have hCsq : 4 + 2 * (c ^ 2 + 2 * max (Ch - c) 0) * (c + 1) ≤ C ^ 2 := by
    have h0 : 0 ≤ 2 * (c ^ 2 + 2 * max (Ch - c) 0) * (c + 1) := by
      have := le_max_right (Ch - c) 0
      positivity
    nlinarith
  have hr0 : (0 : ℝ) ≤ (Fm.D x i).R.rS := by positivity
  have hm2 : (2 : ℝ) ≤ (Fm.D x i).R.m := by rw [rows_m_cast]; linarith
  have hf1 : (1 : ℝ) ≤ (Fm.D x i).R.f := by exact_mod_cast rows_f_pos (Fm.D x i)
  have hL1 := d_one_le_L (Fm.D x i) (Fm.L x i)
  have hkm : ((Fm.D x i).R.m : ℝ) + 3 ≤ (Fm.D x i).R.k := by exact_mod_cast (Fm.D x i).R.m_add_three_le_k
  have ha5 : |C2| * ((Fm.D x i).R.m : ℝ) ^ 5 ≤ (Fm.D x i).R.k := by
    refine le_trans ?_ (Hk x gk i)
    have e2 : ((Fm.D x i).R.m : ℝ) ^ 5 ≤ ((Fm.D x i).R.m : ℝ) ^ 5 * (Fm.D x i).R.f * (Fm.L x i).sc.L := by
      have h5 : 0 ≤ ((Fm.D x i).R.m : ℝ) ^ 5 := by positivity
      nlinarith [mul_nonneg h5 (by linarith : 0 ≤ ((Fm.D x i).R.f : ℝ) - 1),
        mul_nonneg (mul_nonneg h5 (by linarith : 0 ≤ ((Fm.D x i).R.f : ℝ))) (by linarith : 0 ≤ (Fm.L x i).sc.L - 1)]
    calc |C2| * ((Fm.D x i).R.m : ℝ) ^ 5 ≤ |C2| * (((Fm.D x i).R.m : ℝ) ^ 5 * (Fm.D x i).R.f * (Fm.L x i).sc.L) :=
          mul_le_mul_of_nonneg_left e2 (abs_nonneg _)
      _ = |C2| * ((Fm.D x i).R.m : ℝ) ^ 5 * (Fm.D x i).R.f * (Fm.L x i).sc.L := by ring
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = 12 * (c * ((Fm.D x i).R.rS : ℝ) ^ 2) + |C2| * ((Fm.D x i).R.m : ℝ) ^ 2 / 2 +
    |C2| * ((Fm.D x i).R.m : ℝ) ^ 4 + 12 * (((Fm.D x i).R.rS : ℝ) + 1) ^ 2 := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [hadef]; positivity
  have hqb := decay_length_sufficient (m := (Fm.D x i).R.m) (k := (Fm.D x i).R.k) (r := (Fm.D x i).R.rS) (c := c) (B := |C2|)
    (rows_m_cast _) hr0 hkm hc0 (abs_nonneg _) ha5
  have hqb' : (((Fm.D x i).R.rS : ℝ) + 1) * a + 1 ≤ (9 * c + 3) * (Fm.D x i).R.k * ((Fm.D x i).R.m : ℝ) ^ 2 := by
    rw [hadef]; exact hqb
  have hra0 : 0 ≤ (((Fm.D x i).R.rS : ℝ) + 1) * a := by positivity
  have hyp : rows_Hyps (Y x hx1 i u u') (sC' Fm) (sCl Fm) Cg cb Cu cT CT C0 A c (9 * c + 3) Ca C2 Ch (1 / 2) (1 / 4)
      ⌈(((Fm.D x i).R.rS : ℝ) + 1) * a⌉₊ :=
    { hH := hH
      hC3 := H20x x g20 i u u'
      hHH := rows_stHH_mono (by linarith [le_abs_self cH]) (by linarith [neg_abs_le cH]) (H27 x g27 i u u')
      hV := rows_stVol_mono _ (by linarith [le_abs_self cV]) (by linarith [neg_abs_le cV]) (HV x gV i hx1 u u')
      hDEC := (HAx x gA i).2.2.2.2.2.2.2
      ha := h10a x i
      hb := H10 x g10 i
      hp := (HAx x gA i).2.2.1
      hpp := (HAx x gA i).2.2.2.2.2.1
      h6 := H6 x g6 i
      hδ := by norm_num
      hThA := h14 x i u u'
      hT := (hT x hx1 i u u').1
      hG0 := (hT x hx1 i u u').2.1
      hE := (hT x hx1 i u u').2.2
      hc := hc0
      hCh := hCh
      hdim := rows_dim_pos (Y x hx1 i u u') hH.1 (H8 x g8 i u u' hH)
      hq := by linarith [(Nat.ceil_lt_add_one hra0).le] }
  refine corank_one_bound_of_injective_terms _ hyp (switch_bound_mono_constant k5 (H4 x g4 i u u')) (partner_count_bound_mono_constant k6 (H21 x g21 i u u'))
    (hTI x hx1 i u u') (hBL x i u u') (H7 x g7 i) le_rfl (by norm_num) le_rfl hCa (Hc x gc i) ?_ q1 q2
    (by rw [Fm.CGam_eq]; exact q3) hCsq
  rw [le_div_iff₀ (by positivity)]
  have h1 := Nat.le_ceil ((((Fm.D x i).R.rS : ℝ) + 1) * a)
  have h2 : C2 * ((Fm.D x i).R.m : ℝ) ^ 2 / 2 ≤ |C2| * ((Fm.D x i).R.m : ℝ) ^ 2 / 2 := by
    have := le_abs_self C2
    gcongr
  have h3 : |C2 * ((Fm.D x i).R.m : ℝ) ^ 4| = |C2| * ((Fm.D x i).R.m : ℝ) ^ 4 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) ^ 4)]
  calc _ ≤ a * (((Fm.D x i).R.rS : ℝ) + 1) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hadef, h3]; linarith
    _ = (((Fm.D x i).R.rS : ℝ) + 1) * a := by ring
    _ ≤ _ := h1

end Fam

end Formalism.MainNotions.BridgeLemma₂

end
