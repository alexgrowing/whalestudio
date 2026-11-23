import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsOneC

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section One2

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

variable {C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm : ℝ} {q : ℕ}

theorem relevant_of_good_gram {Z : GramM D} (hZ : wordPairGramGood X u u' large₂ c Z) : RelZ D Z := by
  obtain ⟨t, hG, hr, hE, _⟩ := hZ
  exact rows_RelZ_inv hE (rows_RelZ_term X t hG hr)

theorem switchBound_nonneg (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q) {Z : GramM D}
    (hZ : wordPairGramGood X u u' large₂ c Z) : 0 ≤ wordPairSwapBound D large₂ u u' c Z := by
  unfold wordPairSwapBound
  have h1 := rows_one_le_HHZ D large₂ h.hc Z
  have h2 := (rows_nZ_pos Y h hZ).le
  unfold wordPairGramNorm at h2
  exact mul_nonneg (by positivity) h2

theorem fourthMomentBound_nonneg (D : D7) (large₂ : SizeData₂ D) (hc : 0 ≤ c) (x y : GramM D) : 0 ≤ gramPairQuadrupleBound D large₂ c x y := by
  unfold gramPairQuadrupleBound
  have := rows_one_le_HHZ D large₂ hc x
  have := rows_one_le_HHZ D large₂ hc y
  positivity

theorem corank_one_pair_count (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q)
    (hSW : UnitaryVolumeMass.stSW D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c) (hC4 : UnitaryVolumeMass.PartnerCountBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c)
    (hF : rowsSingleFibre X Y) (hF' : wordPairTermSingleFibre X Y) (x y : GramM D) (hx : wordPairGramGood X u u' large₂ c x)
    (hy : wordPairGramGood X u u' large₂ c y) (S' : Finset (D.s.Pair u u'))
    (hS' : ∀ p ∈ S', clsOne p ∧ D.s.relevant (D.s.pfst p) ∧ D.s.relevant (D.s.psnd p) ∧
      ZEquiv (termGramMatrix X (D.s.pfst p)) x ∧ ZEquiv (termGramMatrix X (D.s.psnd p)) y) :
    ∑ p ∈ S', X.wRow p ≤ massRows D Y.F0 Y.what₂ * twoLabelCount D large₂ u u' c x y := by
  unfold twoLabelCount
  rw [mul_min_of_nonneg _ _ (rows_massRows_nonneg Y)]
  refine le_min ?_ ?_
  · refine rows_countOne Y h.hH hSW hC4 hF x y (relevant_of_good_gram hx) (relevant_of_good_gram hy) (switchBound_nonneg Y h hx)
      (fourthMomentBound_nonneg D large₂ h.hc x y) S' fun p hp => ?_
    obtain ⟨⟨g1, g2, n1, n2, s, _⟩, r1, r2, e1, e2⟩ := hS' p hp
    exact ⟨g1, g2, n1, n2, s, e1, e2, rows_RelZ_term X _ g1 r1, (rows_HHZ_inv e1 _ _).symm⟩
  · refine rows_countOne' Y h.hH hSW hC4 hF' x y (relevant_of_good_gram hx) (relevant_of_good_gram hy) (switchBound_nonneg Y h hy)
      (fourthMomentBound_nonneg D large₂ h.hc y x) S' fun p hp => ?_
    obtain ⟨⟨g1, g2, n1, n2, s, _⟩, r1, r2, e1, e2⟩ := hS' p hp
    exact ⟨g1, g2, n1, n2, s, e1, e2, rows_RelZ_term X _ g2 r2, (rows_HHZ_inv e2 _ _).symm⟩

theorem twoLabelCount_mul_amplitude_le (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q)
    (hq1 : 12 * (c * (D.R.rS : ℝ) ^ 2) + C2 * (D.R.m : ℝ) ^ 2 / 2 + |C2 * (D.R.m : ℝ) ^ 4| +
      12 * ((D.R.rS : ℝ) + 1) ^ 2 ≤ (q : ℝ) / ((D.R.rS : ℝ) + 1))
    (x y : GramM D) (hx : wordPairGramGood X u u' large₂ c x) (hy : wordPairGramGood X u u' large₂ c y) :
    twoLabelCount D large₂ u u' c x y * (smallTermAmplitude D large₂ u u' c C2 Ch δ C0 q x * rows_al D large₂ u u' c C2 Ch δ q y) ≤
      labelPairConstant D large₂ u u' c C2 Ch δ C0 * (sizeZ D large₂.sc.b Ch x ^ (-(12 * ((D.R.rS : ℝ) + 1) ^ 2)) *
        sizeZ D large₂.sc.b Ch y ^ (-(12 * ((D.R.rS : ℝ) + 1) ^ 2))) := by
  have hrd := d_rdE_pos h.hH.1
  have hb2 := d_two_le_b D large₂
  have hg : 0 ≤ gg D := by linarith [two_le_gg_of_count_hypotheses h.hH.1]
  have hC0 : 0 ≤ C0 := by linarith [h.hH.1.2.2]
  have hΓ : 0 < GamS D large₂ := by unfold GamS; exact Real.exp_pos _
  have hcr : 0 ≤ c * (D.R.rS : ℝ) ^ 2 := mul_nonneg h.hc (by positivity)
  unfold smallTermAmplitude rows_al labelPairConstant
  refine mul_sqrt_div_mul_sqrt_div_le (a2 := C2 * (D.R.m : ℝ) ^ 2) (a4 := C2 * (D.R.m : ℝ) ^ 4)
    (dq := 2 * (q : ℝ) / ((D.R.rS : ℝ) + 1)) (hS₁ := HHZ D large₂.sc.b c x) (hS₂ := HHZ D large₂.sc.b c y)
    (h4₁ := HHZ D large₂.sc.b c x) (h4₂ := HHZ D large₂.sc.b c y) (hV₁ := HHZ D large₂.sc.b c x) (hV₂ := HHZ D large₂.sc.b c y)
    (rows_P_one_le D large₂ c Ch) (rows_one_le_sizeZ _ _ _) (rows_one_le_sizeZ _ _ _)
    (rows_one_le_HHZ D large₂ h.hc x) (rows_one_le_HHZ D large₂ h.hc y) (rows_one_le_HHZ D large₂ h.hc x) (rows_one_le_HHZ D large₂ h.hc y)
    (rows_one_le_HHZ D large₂ h.hc x) (rows_one_le_HHZ D large₂ h.hc y)
    (rows_HHZ_cmp hrd (by linarith) c Ch x) (rows_HHZ_cmp hrd (by linarith) c Ch y)
    (rows_HHZ_cmp hrd (by linarith) c Ch x) (rows_HHZ_cmp hrd (by linarith) c Ch y)
    (rows_HHZ_cmp hrd (by linarith) c Ch x) (rows_HHZ_cmp hrd (by linarith) c Ch y) hcr hcr hcr hΓ.le
    (by unfold logHeightExp; exact (Real.exp_pos _).le) (mul_nonneg (by linarith [h.hδ]) (rows_rDD_nonneg D u'))
    (smallTermBound_nonneg D large₂ hg u u' hC0) (rows_nZ_pos Y h hx) (rows_nZ_pos Y h hy) (pow_nonneg h.hc _) ?_ ?_ ?_ ?_ ?_
  · unfold twoLabelCount
    exact (min_le_left _ _).trans (le_of_eq (by unfold wordPairSwapBound gramPairQuadrupleBound wordPairGramNorm; rfl))
  · unfold twoLabelCount
    exact (min_le_right _ _).trans (le_of_eq (by unfold wordPairSwapBound gramPairQuadrupleBound wordPairGramNorm; rfl))
  · unfold smallTermLoss; rfl
  · unfold rows_l; rfl
  · have e : 2 * (q : ℝ) / ((D.R.rS : ℝ) + 1) / 2 = (q : ℝ) / ((D.R.rS : ℝ) + 1) := by ring
    rw [e]; linarith

theorem labelPairConstant_nonneg (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q) :
    0 ≤ labelPairConstant D large₂ u u' c C2 Ch δ C0 := by
  have hP1 := rows_P_one_le D large₂ c Ch
  have hτ0 : 0 ≤ (1 + δ) * rDD D u' := mul_nonneg (by linarith [h.hδ]) (rows_rDD_nonneg D u')
  have hGam0 : 0 < GamS D large₂ := by unfold GamS; exact Real.exp_pos _
  have hEx : 0 < logHeightExp D large₂ C2 := by unfold logHeightExp; exact Real.exp_pos _
  have := h.hc
  unfold labelPairConstant
  positivity

theorem twoLabelCount_comm (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (c : ℝ) (x y : GramM D) :
    twoLabelCount D large₂ u u' c x y = twoLabelCount D large₂ u u' c y x := by
  unfold twoLabelCount; exact min_comm _ _

theorem corank_one_first_half (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q)
    (hSW : UnitaryVolumeMass.stSW D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c) (hC4 : UnitaryVolumeMass.PartnerCountBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c)
    (hF : rowsSingleFibre X Y) (hF' : wordPairTermSingleFibre X Y) (h7 : VanishingOnXAndXPlus.adm7 D large₂ C' Cl Cg cb Cu cT CT C0)
    (hδ2 : δ ≤ 1 / 2) (hδm0 : 0 ≤ δm) (hδm : δm ≤ 1 / 4) (hCa : 0 ≤ Ca) (hCak : (max Ca 1) ^ 3 ≤ D.R.k)
    (hq1 : 12 * (c * (D.R.rS : ℝ) ^ 2) + C2 * (D.R.m : ℝ) ^ 2 / 2 + |C2 * (D.R.m : ℝ) ^ 4| +
      12 * ((D.R.rS : ℝ) + 1) ^ 2 ≤ (q : ℝ) / ((D.R.rS : ℝ) + 1))
    (S : Finset (D.s.Pair u u'))
    (hS : ∀ p ∈ S, (clsOne p ∧ D.s.relevant (D.s.pfst p) ∧ D.s.relevant (D.s.psnd p)) ∧ IsSmallTerm Y (D.s.pfst p)) :
    ∑ p ∈ S, wP X p ≤ massRows D Y.F0 Y.what₂ * dimPi (hc := D.hcW) u *
      (labelPairConstant D large₂ u u' c C2 Ch δ C0 * rows_Phi D large₂ c Ch ^ 2) := by
  have sp1 : ∀ p ∈ S, ZEquiv (termGramMatrix X (D.s.pfst p)) (termReducedGramMatrix Y h.hH h.hHH (D.s.pfst p)) ∧
      wordPairGramGood X u u' large₂ c (termReducedGramMatrix Y h.hH h.hHH (D.s.pfst p)) := fun p hp =>
    rows_Zr_spec Y h.hH h.hHH _ (hS p hp).1.1.1 (hS p hp).1.2.1
  have sp2 : ∀ p ∈ S, ZEquiv (termGramMatrix X (D.s.psnd p)) (termReducedGramMatrix Y h.hH h.hHH (D.s.psnd p)) ∧
      wordPairGramGood X u u' large₂ c (termReducedGramMatrix Y h.hH h.hHH (D.s.psnd p)) := fun p hp =>
    rows_Zr_spec Y h.hH h.hHH _ (hS p hp).1.1.2.1 (hS p hp).1.2.2
  have key := weighted_sum_le_of_fibre_counts S (fun p => X.wRow p) (fun p => aT X (D.s.pfst p) / Real.sqrt (dimPi (hc := D.hcW) u))
    (fun p => aT X (D.s.psnd p) / Real.sqrt (dimPi (hc := D.hcW) u)) (fun p => termReducedGramMatrix Y h.hH h.hHH (D.s.pfst p))
    (fun p => termReducedGramMatrix Y h.hH h.hHH (D.s.psnd p)) (massRows D Y.F0 Y.what₂) (labelPairConstant D large₂ u u' c C2 Ch δ C0)
    (rows_Phi D large₂ c Ch) (fun x y => twoLabelCount D large₂ u u' c x y)
    (smallTermAmplitude D large₂ u u' c C2 Ch δ C0 q) (rows_al D large₂ u u' c C2 Ch δ q)
    (fun Z => sizeZ D large₂.sc.b Ch Z ^ (-(12 * ((D.R.rS : ℝ) + 1) ^ 2)))
    (rows_massRows_nonneg Y) (labelPairConstant_nonneg Y h)
    (fun p _ => (X.wRow_pos p).le) (fun p _ => div_nonneg (aT_nonneg _ _) (Real.sqrt_nonneg _))
    (fun p hp => small_term_amplitude_le Y h h7 hδ2 hδm0 hδm hCa hCak _ (hS p hp).1.1.1 (hS p hp).1.2.1 (hS p hp).2)
    (fun p hp => rows_nd_term Y h _ (hS p hp).1.1.2.1 (hS p hp).1.2.2)
    (by
      rintro x y ⟨p1, hp1, rfl⟩ ⟨p2, hp2, rfl⟩ S' hS' hl
      refine corank_one_pair_count Y h hSW hC4 hF hF' _ _ (sp1 p1 hp1).2 (sp2 p2 hp2).2 S' fun p hp => ?_
      refine ⟨(hS p (hS' hp)).1.1, (hS p (hS' hp)).1.2.1, (hS p (hS' hp)).1.2.2, ?_, ?_⟩
      · rw [← (hl p hp).1]; exact (sp1 p (hS' hp)).1
      · rw [← (hl p hp).2]; exact (sp2 p (hS' hp)).1)
    (by
      rintro x y ⟨p1, hp1, rfl⟩ ⟨p2, hp2, rfl⟩
      exact twoLabelCount_mul_amplitude_le Y h hq1 _ _ (sp1 p1 hp1).2 (sp2 p2 hp2).2)
    (fun x => Real.sqrt_nonneg _) (fun x => Real.sqrt_nonneg _)
    (fun x => Real.rpow_nonneg (le_trans zero_le_one (rows_one_le_sizeZ _ _ _)) _)
    (fun 𝒵 h𝒵 => rows_nd_size Y h 𝒵 fun Z hZ => by obtain ⟨p, hp, rfl⟩ := h𝒵 Z hZ; exact (sp1 p hp).2)
    (fun 𝒵 h𝒵 => rows_nd_size Y h 𝒵 fun Z hZ => by obtain ⟨p, hp, rfl⟩ := h𝒵 Z hZ; exact (sp2 p hp).2)
  rw [rows_wP_sum h.hdim S]
  calc dimPi (hc := D.hcW) u * _
      ≤ dimPi (hc := D.hcW) u * (massRows D Y.F0 Y.what₂ * (labelPairConstant D large₂ u u' c C2 Ch δ C0 * rows_Phi D large₂ c Ch ^ 2)) :=
        mul_le_mul_of_nonneg_left key h.hdim.le
    _ = _ := by ring

theorem corank_one_second_half (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q)
    (hSW : UnitaryVolumeMass.stSW D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c) (hC4 : UnitaryVolumeMass.PartnerCountBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c)
    (hF : rowsSingleFibre X Y) (hF' : wordPairTermSingleFibre X Y) (h7 : VanishingOnXAndXPlus.adm7 D large₂ C' Cl Cg cb Cu cT CT C0)
    (hδ2 : δ ≤ 1 / 2) (hδm0 : 0 ≤ δm) (hδm : δm ≤ 1 / 4) (hCa : 0 ≤ Ca) (hCak : (max Ca 1) ^ 3 ≤ D.R.k)
    (hq1 : 12 * (c * (D.R.rS : ℝ) ^ 2) + C2 * (D.R.m : ℝ) ^ 2 / 2 + |C2 * (D.R.m : ℝ) ^ 4| +
      12 * ((D.R.rS : ℝ) + 1) ^ 2 ≤ (q : ℝ) / ((D.R.rS : ℝ) + 1))
    (S : Finset (D.s.Pair u u'))
    (hS : ∀ p ∈ S, (clsOne p ∧ D.s.relevant (D.s.pfst p) ∧ D.s.relevant (D.s.psnd p)) ∧ IsSmallTerm Y (D.s.psnd p)) :
    ∑ p ∈ S, wP X p ≤ massRows D Y.F0 Y.what₂ * dimPi (hc := D.hcW) u *
      (labelPairConstant D large₂ u u' c C2 Ch δ C0 * rows_Phi D large₂ c Ch ^ 2) := by
  have sp1 : ∀ p ∈ S, ZEquiv (termGramMatrix X (D.s.pfst p)) (termReducedGramMatrix Y h.hH h.hHH (D.s.pfst p)) ∧
      wordPairGramGood X u u' large₂ c (termReducedGramMatrix Y h.hH h.hHH (D.s.pfst p)) := fun p hp =>
    rows_Zr_spec Y h.hH h.hHH _ (hS p hp).1.1.1 (hS p hp).1.2.1
  have sp2 : ∀ p ∈ S, ZEquiv (termGramMatrix X (D.s.psnd p)) (termReducedGramMatrix Y h.hH h.hHH (D.s.psnd p)) ∧
      wordPairGramGood X u u' large₂ c (termReducedGramMatrix Y h.hH h.hHH (D.s.psnd p)) := fun p hp =>
    rows_Zr_spec Y h.hH h.hHH _ (hS p hp).1.1.2.1 (hS p hp).1.2.2
  have key := weighted_sum_le_of_fibre_counts S (fun p => X.wRow p) (fun p => aT X (D.s.pfst p) / Real.sqrt (dimPi (hc := D.hcW) u))
    (fun p => aT X (D.s.psnd p) / Real.sqrt (dimPi (hc := D.hcW) u)) (fun p => termReducedGramMatrix Y h.hH h.hHH (D.s.pfst p))
    (fun p => termReducedGramMatrix Y h.hH h.hHH (D.s.psnd p)) (massRows D Y.F0 Y.what₂) (labelPairConstant D large₂ u u' c C2 Ch δ C0)
    (rows_Phi D large₂ c Ch) (fun x y => twoLabelCount D large₂ u u' c x y)
    (rows_al D large₂ u u' c C2 Ch δ q) (smallTermAmplitude D large₂ u u' c C2 Ch δ C0 q)
    (fun Z => sizeZ D large₂.sc.b Ch Z ^ (-(12 * ((D.R.rS : ℝ) + 1) ^ 2)))
    (rows_massRows_nonneg Y) (labelPairConstant_nonneg Y h)
    (fun p _ => (X.wRow_pos p).le) (fun p _ => div_nonneg (aT_nonneg _ _) (Real.sqrt_nonneg _))
    (fun p hp => rows_nd_term Y h _ (hS p hp).1.1.1 (hS p hp).1.2.1)
    (fun p hp => small_term_amplitude_le Y h h7 hδ2 hδm0 hδm hCa hCak _ (hS p hp).1.1.2.1 (hS p hp).1.2.2 (hS p hp).2)
    (by
      rintro x y ⟨p1, hp1, rfl⟩ ⟨p2, hp2, rfl⟩ S' hS' hl
      refine corank_one_pair_count Y h hSW hC4 hF hF' _ _ (sp1 p1 hp1).2 (sp2 p2 hp2).2 S' fun p hp => ?_
      refine ⟨(hS p (hS' hp)).1.1, (hS p (hS' hp)).1.2.1, (hS p (hS' hp)).1.2.2, ?_, ?_⟩
      · rw [← (hl p hp).1]; exact (sp1 p (hS' hp)).1
      · rw [← (hl p hp).2]; exact (sp2 p (hS' hp)).1)
    (by
      rintro x y ⟨p1, hp1, rfl⟩ ⟨p2, hp2, rfl⟩
      have := twoLabelCount_mul_amplitude_le Y h hq1 _ _ (sp2 p2 hp2).2 (sp1 p1 hp1).2
      rw [twoLabelCount_comm] at this
      rw [mul_comm (rows_al D large₂ u u' c C2 Ch δ q _), mul_comm (sizeZ D large₂.sc.b Ch (termReducedGramMatrix Y h.hH h.hHH (D.s.pfst p1)) ^ _)]
      exact this)
    (fun x => Real.sqrt_nonneg _) (fun x => Real.sqrt_nonneg _)
    (fun x => Real.rpow_nonneg (le_trans zero_le_one (rows_one_le_sizeZ _ _ _)) _)
    (fun 𝒵 h𝒵 => rows_nd_size Y h 𝒵 fun Z hZ => by obtain ⟨p, hp, rfl⟩ := h𝒵 Z hZ; exact (sp1 p hp).2)
    (fun 𝒵 h𝒵 => rows_nd_size Y h 𝒵 fun Z hZ => by obtain ⟨p, hp, rfl⟩ := h𝒵 Z hZ; exact (sp2 p hp).2)
  rw [rows_wP_sum h.hdim S]
  calc dimPi (hc := D.hcW) u * _
      ≤ dimPi (hc := D.hcW) u * (massRows D Y.F0 Y.what₂ * (labelPairConstant D large₂ u u' c C2 Ch δ C0 * rows_Phi D large₂ c Ch ^ 2)) :=
        mul_le_mul_of_nonneg_left key h.hdim.le
    _ = _ := by ring

theorem small_term_of_corank_one_pair (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A) (p : D.s.Pair u u') (hp : clsOne p)
    (hr1 : D.s.relevant (D.s.pfst p)) (hr2 : D.s.relevant (D.s.psnd p)) :
    IsSmallTerm Y (D.s.pfst p) ∨ IsSmallTerm Y (D.s.psnd p) := by
  obtain ⟨hG1, hG2, hg1, hg2, hs, hns⟩ := hp
  have hSt := hH.2.1
  have t1 := (rows_isTermF Y (D.s.pfst p) hG1).1
  have t2 := (rows_isTermF Y (D.s.psnd p) hG2).1
  rw [← X.pLam p] at t2
  rw [← Y.fl_eq (D.s.pfst p)] at t1 t2
  have gen1 := (X.gen_iff _).1 hg1
  have gen2 := (X.gen_iff _).1 hg2
  rw [← X.pLam p, ← X.pfl p] at gen2
  have hB := Formalism.MainNotions.LatticeGluingRadicals.theorem_B_section D u (Tu D u') _ _ _ _ _ (X.fixed _) (VanishingOnXAndXPlus.primeHyp_of_stand D u u' hSt) t1 t2
    (X.isPair p) (by rw [← X.s0_eq p]; exact hs) gen1 gen2
  rcases hB with hsc | hB
  · exact absurd ((X.scal_iff p hs).2 hsc) hns
  · exact rowsT_small Y hSt (d_rdE_pos hH.1) _ _ hG1 hr1 hG2 hr2 hB

open Classical in

theorem corank_one_bound_of_fibres (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q)
    (hSW : UnitaryVolumeMass.stSW D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c) (hC4 : UnitaryVolumeMass.PartnerCountBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c)
    (hF : rowsSingleFibre X Y) (hF' : wordPairTermSingleFibre X Y) (h7 : VanishingOnXAndXPlus.adm7 D large₂ C' Cl Cg cb Cu cT CT C0)
    (hδ2 : δ ≤ 1 / 2) (hδm0 : 0 ≤ δm) (hδm : δm ≤ 1 / 4) (hCa : 0 ≤ Ca) (hCak : (max Ca 1) ^ 3 ≤ D.R.k)
    (hq1 : 12 * (c * (D.R.rS : ℝ) ^ 2) + C2 * (D.R.m : ℝ) ^ 2 / 2 + |C2 * (D.R.m : ℝ) ^ 4| +
      12 * ((D.R.rS : ℝ) + 1) ^ 2 ≤ (q : ℝ) / ((D.R.rS : ℝ) + 1)) :
    RowBound X Y clsOne (corankOneBound D large₂ u u' c C2 Ch δ C0) := by
  refine rowBound_relevant Y (fun p hp => ⟨hp.1, hp.2.1⟩) ?_
  intro S hS
  rw [← Finset.sum_filter_add_sum_filter_not S (fun p => IsSmallTerm Y (D.s.pfst p))]
  have a1 := corank_one_first_half Y h hSW hC4 hF hF' h7 hδ2 hδm0 hδm hCa hCak hq1
    (S.filter (fun p => IsSmallTerm Y (D.s.pfst p))) fun p hp =>
      ⟨hS p (Finset.mem_filter.1 hp).1, (Finset.mem_filter.1 hp).2⟩
  have a2 := corank_one_second_half Y h hSW hC4 hF hF' h7 hδ2 hδm0 hδm hCa hCak hq1
    (S.filter (fun p => ¬ IsSmallTerm Y (D.s.pfst p))) fun p hp => by
      have hp1 := hS p (Finset.mem_filter.1 hp).1
      refine ⟨hp1, ?_⟩
      rcases small_term_of_corank_one_pair Y h.hH p hp1.1 hp1.2.1 hp1.2.2 with h' | h'
      · exact absurd h' (Finset.mem_filter.1 hp).2
      · exact h'
  unfold corankOneBound
  linarith

end One2

end Formalism.MainNotions.BridgeLemma₂

end
