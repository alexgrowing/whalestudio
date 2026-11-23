import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsLab

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ND

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

include Y in

theorem rows_thmA (hThA : VanishingOnXAndXPlus.adm14 D u u') (hSt : Cnt.Stand D u u') (p : D.s.Pair u u')
    (hG1 : D.s.Gterm (D.s.pfst p) ≠ 0) (hG2 : D.s.Gterm (D.s.psnd p) ≠ 0) (hs : 2 ≤ D.s.s0 p) :
    UnitaryVolumeMass.ThmA D (X.abelian₂ (D.s.pfst p)) (Tu D u) (Tu D u') (gS D) (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p))
      (X.fl' (D.s.psnd p)) (X.beta p) := by
  have t1 := (rows_isTermF Y (D.s.pfst p) hG1).1
  have t2 := (rows_isTermF Y (D.s.psnd p) hG2).1
  rw [← X.pLam p] at t2
  rw [← Y.fl_eq (D.s.pfst p)] at t1 t2
  refine hThA _ _ _ _ _ (X.fixed _) (VanishingOnXAndXPlus.primeHyp_of_stand D u u' hSt) t1 t2 (X.isPair p) ?_
  rw [← X.s0_eq p]; exact hs

include Y in

theorem rows_thmA_nd (hThA : VanishingOnXAndXPlus.adm14 D u u') (hSt : Cnt.Stand D u u') (hG0 : @LatticeDeterminantFactorization D X u u') (p : D.s.Pair u u')
    (hG1 : D.s.Gterm (D.s.pfst p) ≠ 0) (hG2 : D.s.Gterm (D.s.psnd p) ≠ 0) (hs : 2 ≤ D.s.s0 p) (hnd : ndP X p) :
    pairDeterminant X p ≤ (2 / gg D) ^ ((D.s.s0 p - 1) * D.R.f) *
      Real.sqrt (wordPairGramProduct D u u' (termGramMatrix X (D.s.pfst p)) * wordPairGramProduct D u u' (termGramMatrix X (D.s.psnd p))) := by
  have h := (rows_thmA Y hThA hSt p hG1 hG2 hs).1 hnd
  have e1 : G0 (X.abelian₂ (D.s.pfst p)) (gS D) (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p)) =
      wordPairGramProduct D u u' (termGramMatrix X (D.s.pfst p)) := hG0 (D.s.pfst p) hG1
  have e2 : G0 (X.abelian₂ (D.s.psnd p)) (gS D) (X.fl (D.s.psnd p)) (X.fl' (D.s.psnd p)) =
      wordPairGramProduct D u u' (termGramMatrix X (D.s.psnd p)) := hG0 (D.s.psnd p) hG2
  rw [← X.pLam p, ← X.pfl p] at e2
  rw [e1, e2, ← X.s0_eq p, ← rows_gg_eq] at h
  exact h

def rows_l (D : D7) (large₂ : SizeData₂ D) (c C2 Ch : ℝ) (q : ℕ) (Z : GramM D) : ℝ :=
  (HHZ D large₂.sc.b c Z ^ (c * (D.R.rS : ℝ) ^ 2)) ^ 2 *
    (GamS D large₂ * sizeZ D large₂.sc.b Ch Z ^ (C2 * (D.R.m : ℝ) ^ 2)) *
    sizeZ D large₂.sc.b Ch Z ^ (-(2 * (q : ℝ) / ((D.R.rS : ℝ) + 1)))

def rows_P (D : D7) (large₂ : SizeData₂ D) (c Ch : ℝ) : ℝ := large₂.sc.b ^ pairCountExponentShift D c Ch

def rows_al (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (c C2 Ch δ : ℝ) (q : ℕ) (Z : GramM D) : ℝ :=
  Real.sqrt (rows_l D large₂ c C2 Ch q Z * ((1 + δ) * rDD D u') / wordPairGramNorm D u u' Z)

def rows_DeZ (D : D7) (u u' : D.what₂.Word) (s : ℕ) (x y : GramM D) : ℝ :=
  (2 / gg D) ^ ((s - 1) * D.R.f) * Real.sqrt (wordPairGramProduct D u u' x * wordPairGramProduct D u u' y)

def rows_R (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (c Ch δ : ℝ) (s : ℕ) : ℝ :=
  (2 / gg D) ^ ((s - 1) * D.R.k * D.R.f) * ((D.R.k : ℝ) * D.host.v / (Real.exp 1 * Real.pi)) ^ (D.R.k * D.R.f) *
    (XiS D u (rows_P D large₂ c Ch ^ 2) c s *
      ((rows_P D large₂ c Ch ^ pairCountExponent D c s) ^ 2 * (rows_P D large₂ c Ch ^ (c * (D.R.rS : ℝ) ^ 2)) ^ 2 *
        (c * s * D.R.f) ^ (6 * s * D.R.f) * GamS D large₂)) * ((1 + δ) * rDD D u')

def rows_Phi (D : D7) (large₂ : SizeData₂ D) (c Ch : ℝ) : ℝ := (41 ^ D.R.f * rows_P D large₂ c Ch ^ 3) ^ ((D.R.rS + 1) ^ 2)

def rows_ndB (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (c Ch δ : ℝ) (s : ℕ) : ℝ :=
  rows_R D large₂ u u' c Ch δ s * rows_Phi D large₂ c Ch ^ 2

theorem rows_rDD_nonneg (D : D7) (w : D.what₂.Word) : 0 ≤ rDD D w := by
  unfold rDD; exact div_nonneg (by positivity) (d_Dstar_pos D).le

theorem rows_l_nonneg (D : D7) (large₂ : SizeData₂ D) (c C2 Ch : ℝ) (q : ℕ) (hc : 0 ≤ c) (Z : GramM D) : 0 ≤ rows_l D large₂ c C2 Ch q Z := by
  unfold rows_l
  have h1 := rows_one_le_HHZ D large₂ hc Z
  have h2 := rows_one_le_sizeZ (D := D) large₂.sc.b Ch Z
  have h3 : 0 < GamS D large₂ := by unfold GamS; exact Real.exp_pos _
  positivity

structure rows_Hyps (Y : LoopTie D large₂ X u u' C1) (C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm : ℝ) (q : ℕ) : Prop where
  hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A
  hC3 : UnitaryVolumeMass.MeanFlagPairCount D large₂ u u' C' Cl Cg cb Cu cT CT C0 A 3 c
  hHH : UnitaryVolumeMass.stHH D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c
  hV : VanishingOnXAndXPlus.TermVolumeSmallCellBound D large₂ X u u' C1 Y C' Cl Cg cb Cu cT CT C0 A c
  hDEC : VanishingOnXAndXPlus.adm26 D large₂ C' Cl Cg cb Cu cT CT C0 A C1 Cpr Ca Ch δm
  ha : VanishingOnXAndXPlus.PlaneWaveLetters D
  hb : VanishingOnXAndXPlus.PlaneWaveIsometry D large₂ C' Cl Cg cb Cu cT CT C0
  hp : VanishingOnXAndXPlus.L2LossProductBound D large₂ C' Cl Cg cb Cu cT CT C0 A Ca C2 Ch
  hpp : VanishingOnXAndXPlus.AbsoluteLossProductBound D large₂ C' Cl Cg cb Cu cT CT C0 A Ca C2 Ch
  h6 : VanishingOnXAndXPlus.adm6 D large₂ C' Cl Cg cb Cu cT CT C0 δ
  hδ : 0 ≤ δ
  hThA : VanishingOnXAndXPlus.adm14 D u u'
  hT : TermPtsTie X Y
  hG0 : @LatticeDeterminantFactorization D X u u'
  hE : wordPairEntriesInLattice X u u'
  hc : 0 ≤ c
  hCh : 0 ≤ Ch
  hdim : 0 < dimPi (hc := D.hcW) u
  hq : (q : ℝ) ≤ Cpr * D.R.k * (D.R.m : ℝ) ^ 2

variable {C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm : ℝ} {q : ℕ}

theorem rows_f_pos (D : D7) : 0 < D.R.f := by
  unfold Ranks.f Ranks.n
  have := D.R.ord_pos
  omega

theorem rows_P_one_le (D : D7) (large₂ : SizeData₂ D) (c Ch : ℝ) : 1 ≤ rows_P D large₂ c Ch := by
  unfold rows_P
  exact Real.one_le_rpow (by linarith [d_two_le_b D large₂]) (by unfold pairCountExponentShift; positivity)

theorem pairCountExponent_nonneg (D : D7) {c : ℝ} (hc : 0 ≤ c) (s : ℕ) : 0 ≤ pairCountExponent D c s := by
  unfold pairCountExponent cF lg2f
  have : 0 ≤ Real.logb 2 (2 * (D.R.f : ℝ)) := Real.logb_nonneg (by norm_num) (by
    have : (1 : ℝ) ≤ D.R.f := by exact_mod_cast rows_f_pos D
    linarith)
  positivity

theorem rows_nZ_pos (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q) {Z : GramM D}
    (hZ : wordPairGramGood X u u' large₂ c Z) : 0 < wordPairGramNorm D u u' Z := by
  have e : wordPairGramNorm D u u' Z = LatticeSumBounds.nTot D.R.k D.R.f D.host.v (wordPairGramProduct D u u' Z) (NT D u) := d_nProduct h.hH.1 Z
  rw [e]
  unfold LatticeSumBounds.nTot
  have h1 := gramProductG0_pos Y h.hH.1 h.hT hZ
  have h2 := rows_NT_pos D u
  have hpi := Real.pi_pos
  have hv1 : 1 ≤ D.host.v := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h19, _⟩ := h.hH.1.1
    exact h19
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hv0 : 0 < D.host.v := by linarith
  have hk0 : (0 : ℝ) < D.R.k := by linarith
  positivity

theorem rows_nd_term (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q) (t : D.s.Term u u')
    (hG : D.s.Gterm t ≠ 0) (hrel : D.s.relevant t) :
    aT X t / Real.sqrt (dimPi (hc := D.hcW) u) ≤ rows_al D large₂ u u' c C2 Ch δ q (termReducedGramMatrix Y h.hH h.hHH t) := by
  obtain ⟨hEq, hGood⟩ := rows_Zr_spec Y h.hH h.hHH t hG hrel
  have h1 := rows_term_L2dec Y h.hH h.hDEC h.ha h.hb h.hp h.h6 h.hδ h.hV h.hT h.hCh t hG hrel q h.hq
  rw [← rows_nZ_inv hEq, ← rows_HHZ_inv hEq, ← rows_sizeZ_inv hEq] at h1
  have h2 : aT X t ^ 2 / dimPi (hc := D.hcW) u ≤ rows_l D large₂ c C2 Ch q (termReducedGramMatrix Y h.hH h.hHH t) * ((1 + δ) * rDD D u') /
      wordPairGramNorm D u u' (termReducedGramMatrix Y h.hH h.hHH t) := by
    rw [le_div_iff₀ (rows_nZ_pos Y h hGood)]
    calc aT X t ^ 2 / dimPi (hc := D.hcW) u * wordPairGramNorm D u u' (termReducedGramMatrix Y h.hH h.hHH t)
        = wordPairGramNorm D u u' (termReducedGramMatrix Y h.hH h.hHH t) * aT X t ^ 2 / dimPi (hc := D.hcW) u := by ring
      _ ≤ _ := h1
  have h3 : aT X t / Real.sqrt (dimPi (hc := D.hcW) u) = Real.sqrt (aT X t ^ 2 / dimPi (hc := D.hcW) u) := by
    rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (aT_nonneg X t)]
  rw [h3]
  exact Real.sqrt_le_sqrt h2

theorem rows_DeZ_nonneg (D : D7) (hg : 0 ≤ gg D) (u u' : D.what₂.Word) (s : ℕ) (x y : GramM D) : 0 ≤ rows_DeZ D u u' s x y := by
  unfold rows_DeZ; exact mul_nonneg (by positivity) (Real.sqrt_nonneg _)

theorem rows_massRows_nonneg : 0 ≤ massRows D Y.F0 Y.what₂ :=
  Finset.sum_nonneg fun Λ _ => by unfold Formalism.MainNotions.S.wRow; positivity

theorem rows_nd_count (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q) (s : ℕ) (hs : 2 ≤ s)
    (hsk : s ≤ D.R.k) (x y : GramM D) (gx : wordPairGramGood X u u' large₂ c x) (gy : wordPairGramGood X u u' large₂ c y)
    (S' : Finset (D.s.Pair u u'))
    (hS : ∀ p ∈ S', clsND X s p ∧ ZEquiv (termGramMatrix X (D.s.pfst p)) x ∧ ZEquiv (termGramMatrix X (D.s.psnd p)) y) :
    ∑ p ∈ S', X.wRow p ≤ massRows D Y.F0 Y.what₂ * wordSublatticeTripleBound D large₂ u c x y s (rows_DeZ D u u' s x y) := by
  have hg2 := two_le_gg_of_count_hypotheses h.hH.1
  have hDe0 := rows_DeZ_nonneg D (by linarith) u u' s x y
  by_cases hne : S'.Nonempty
  · obtain ⟨p₀, hp₀⟩ := hne
    have hDe_of : ∀ p ∈ S', pairDeterminant X p ≤ rows_DeZ D u u' s x y := by
      intro p hp
      obtain ⟨⟨hG1, hG2, hs0, hnd⟩, e1, e2⟩ := hS p hp
      have h' := rows_thmA_nd Y h.hThA h.hH.2.1 h.hG0 p hG1 hG2 (by rw [hs0]; exact hs) hnd
      rw [hs0, ← gramProductG0_equiv_invariant e1, ← gramProductG0_equiv_invariant e2] at h'
      exact h'
    have h1 : 1 ≤ rows_DeZ D u u' s x y :=
      le_trans (rows_DetGeOne_of h.hH.2.1 p₀ (hS p₀ hp₀).1.1 (hS p₀ hp₀).1.2.1) (hDe_of p₀ hp₀)
    have h2 : rows_DeZ D u u' s x y ≤ (HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y) ^ (3 : ℝ) := by
      have := (Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.deNonDegBound D.R.f s (gg D) (wordPairGramProduct D u u' x) (wordPairGramProduct D u u' y)
        (HHZ D large₂.sc.b c x) (HHZ D large₂.sc.b c y) hg2 (gramProductG0_pos Y h.hH.1 h.hT gx).le
        (gramProductG0_pos Y h.hH.1 h.hT gy).le (gramProductG0_le_height Y h.hH h.hHH h.hT gx)
        (gramProductG0_le_height Y h.hH h.hHH h.hT gy) (rows_one_le_HHZ D large₂ h.hc x) (rows_one_le_HHZ D large₂ h.hc y)).2
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact this
    obtain ⟨t1, hG1, hr1, hE1, _⟩ := gx
    obtain ⟨t2, hG2, hr2, hE2, _⟩ := gy
    refine rows_count Y h.hH h.hC3 x y (rows_RelZ_inv hE1 (rows_RelZ_term X t1 hG1 hr1))
      (rows_RelZ_inv hE2 (rows_RelZ_term X t2 hG2 hr2)) s hs hsk _ h1 h2
      (rows_c3B_nonneg D large₂ u h.hc x y s hDe0) _ ?_
    intro p hp
    exact ⟨(hS p hp).1.1, (hS p hp).1.2.1, (hS p hp).2.1, (hS p hp).2.2, (hS p hp).1.2.2.1, hDe_of p hp⟩
  · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sum_empty]
    exact mul_nonneg (rows_massRows_nonneg Y) (rows_c3B_nonneg D large₂ u h.hc x y s hDe0)

theorem rows_nd_prod (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q) (s : ℕ) (hs : 2 ≤ s)
    (hq2 : 4 * (c * D.R.k) + 4 * pairCountExponent D c s + 4 * (c * (D.R.rS : ℝ) ^ 2) + C2 * (D.R.m : ℝ) ^ 2 / 2 +
      12 * ((D.R.rS : ℝ) + 1) ^ 2 ≤ (q : ℝ) / ((D.R.rS : ℝ) + 1))
    (x y : GramM D) (gx : wordPairGramGood X u u' large₂ c x) (gy : wordPairGramGood X u u' large₂ c y) :
    wordSublatticeTripleBound D large₂ u c x y s (rows_DeZ D u u' s x y) *
        (rows_al D large₂ u u' c C2 Ch δ q x * rows_al D large₂ u u' c C2 Ch δ q y) ≤
      rows_R D large₂ u u' c Ch δ s * (sizeZ D large₂.sc.b Ch x ^ (-(12 * ((D.R.rS : ℝ) + 1) ^ 2)) *
        sizeZ D large₂.sc.b Ch y ^ (-(12 * ((D.R.rS : ℝ) + 1) ^ 2))) := by
  have hrd := d_rdE_pos h.hH.1
  have hb2 := d_two_le_b D large₂
  have hg2 := two_le_gg_of_count_hypotheses h.hH.1
  have hc := h.hc
  have hv1 : 1 ≤ D.host.v := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h19, _⟩ := h.hH.1.1
    exact h19
  have hk1 : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hτ0 : 0 ≤ (1 + δ) * rDD D u' := mul_nonneg (by linarith [h.hδ]) (rows_rDD_nonneg D u')
  have hGam0 : 0 < GamS D large₂ := by unfold GamS; exact Real.exp_pos _
  have hx1 := rows_one_le_HHZ D large₂ hc x
  have hy1 := rows_one_le_HHZ D large₂ hc y
  have sx1 := rows_one_le_sizeZ (D := D) large₂.sc.b Ch x
  have sy1 := rows_one_le_sizeZ (D := D) large₂.sc.b Ch y
  have hh0 : 0 ≤ HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y := mul_nonneg (by linarith) (by linarith)
  have hP1 := rows_P_one_le D large₂ c Ch
  have cx : HHZ D large₂.sc.b c x ≤ rows_P D large₂ c Ch * sizeZ D large₂.sc.b Ch x ^ 4 := rows_HHZ_cmp hrd (by linarith) c Ch x
  have cy : HHZ D large₂.sc.b c y ≤ rows_P D large₂ c Ch * sizeZ D large₂.sc.b Ch y ^ 4 := rows_HHZ_cmp hrd (by linarith) c Ch y
  have hαsq : ∀ Z, wordPairGramGood X u u' large₂ c Z →
      LatticeSumBounds.nTot D.R.k D.R.f D.host.v (wordPairGramProduct D u u' Z) (NT D u) * rows_al D large₂ u u' c C2 Ch δ q Z ^ 2 ≤
        rows_l D large₂ c C2 Ch q Z * ((1 + δ) * rDD D u') := by
    intro Z hZ
    have e : wordPairGramNorm D u u' Z = LatticeSumBounds.nTot D.R.k D.R.f D.host.v (wordPairGramProduct D u u' Z) (NT D u) := d_nProduct h.hH.1 Z
    rw [← e]
    unfold rows_al
    rw [Real.sq_sqrt (div_nonneg (mul_nonneg (rows_l_nonneg D large₂ c C2 Ch q hc Z) hτ0) (rows_nZ_pos Y h hZ).le),
      mul_div_cancel₀ _ (rows_nZ_pos Y h hZ).ne']
  have n1 := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.nonDegRow D.R.k D.R.f s (gg D) D.host.v (NT D u) (wordPairGramProduct D u u' x) (wordPairGramProduct D u u' y)
    (XiS D u (HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y) c s)
    ((HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y) ^ pairCountExponent D c s * (c * s * D.R.f) ^ (6 * s * D.R.f))
    (wordSublatticeTripleBound D large₂ u c x y s (rows_DeZ D u u' s x y)) (rows_al D large₂ u u' c C2 Ch δ q x) (rows_al D large₂ u u' c C2 Ch δ q y)
    (rows_l D large₂ c C2 Ch q x) (rows_l D large₂ c C2 Ch q y) ((1 + δ) * rDD D u') hk1 (by omega) (by linarith) (by linarith)
    (rows_NT_pos D u) (gramProductG0_pos Y h.hH.1 h.hT gx) (gramProductG0_pos Y h.hH.1 h.hT gy) (rows_XiS_nonneg D u hh0 hc s)
    (by positivity) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hτ0
    (le_of_eq (by unfold wordSublatticeTripleBound pairCountExponent rows_DeZ; ring)) (hαsq x gx) (hαsq y gy)
  have hXi : XiS D u (HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y) c s ≤
      XiS D u (rows_P D large₂ c Ch ^ 2) c s * (sizeZ D large₂.sc.b Ch x * sizeZ D large₂.sc.b Ch y) ^ (4 * (c * D.R.k)) := by
    refine rows_Xi_le D u hh0 (by positivity) (one_le_mul_of_one_le_of_one_le sx1 sy1) hc ?_ s
    calc HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y
        ≤ (rows_P D large₂ c Ch * sizeZ D large₂.sc.b Ch x ^ 4) * (rows_P D large₂ c Ch * sizeZ D large₂.sc.b Ch y ^ 4) :=
          mul_le_mul cx cy (by linarith) (by positivity)
      _ = rows_P D large₂ c Ch ^ 2 * (sizeZ D large₂.sc.b Ch x * sizeZ D large₂.sc.b Ch y) ^ 4 := by ring
  have he : 4 * (c * D.R.k) + 4 * pairCountExponent D c s + 4 * (c * (D.R.rS : ℝ) ^ 2) + C2 * (D.R.m : ℝ) ^ 2 / 2 -
      2 * (q : ℝ) / ((D.R.rS : ℝ) + 1) / 2 ≤ -(12 * ((D.R.rS : ℝ) + 1) ^ 2) := by
    have e : 2 * (q : ℝ) / ((D.R.rS : ℝ) + 1) / 2 = (q : ℝ) / ((D.R.rS : ℝ) + 1) := by ring
    rw [e]; linarith
  have n2 := rows_num_pair (P := rows_P D large₂ c Ch) (σ₁ := sizeZ D large₂.sc.b Ch x) (σ₂ := sizeZ D large₂.sc.b Ch y)
    (h₁ := HHZ D large₂.sc.b c x) (h₂ := HHZ D large₂.sc.b c y)
    (cr := c * (D.R.rS : ℝ) ^ 2) (Γ := GamS D large₂) (a2 := C2 * (D.R.m : ℝ) ^ 2)
    (dq := 2 * (q : ℝ) / ((D.R.rS : ℝ) + 1)) (E1 := pairCountExponent D c s) (F6 := (c * s * D.R.f) ^ (6 * s * D.R.f))
    (XiH := XiS D u (HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y) c s) (XiP := XiS D u (rows_P D large₂ c Ch ^ 2) c s)
    (ck := c * D.R.k) (e := 12 * ((D.R.rS : ℝ) + 1) ^ 2) (l₁ := rows_l D large₂ c C2 Ch q x) (l₂ := rows_l D large₂ c C2 Ch q y)
    hP1 sx1 sy1 hx1 hy1 cx cy (by positivity) hGam0.le (pairCountExponent_nonneg D hc s) (by positivity)
    (rows_XiS_nonneg D u hh0 hc s) hXi rfl rfl he
  have hA0 : 0 ≤ (2 / gg D) ^ ((s - 1) * D.R.k * D.R.f) *
      ((D.R.k : ℝ) * D.host.v / (Real.exp 1 * Real.pi)) ^ (D.R.k * D.R.f) := by
    have hpi := Real.pi_pos
    have : 0 ≤ gg D := by linarith
    have : 0 ≤ D.host.v := by linarith
    positivity
  calc wordSublatticeTripleBound D large₂ u c x y s (rows_DeZ D u u' s x y) *
        (rows_al D large₂ u u' c C2 Ch δ q x * rows_al D large₂ u u' c C2 Ch δ q y)
      = wordSublatticeTripleBound D large₂ u c x y s (rows_DeZ D u u' s x y) * rows_al D large₂ u u' c C2 Ch δ q x *
          rows_al D large₂ u u' c C2 Ch δ q y := by ring
    _ ≤ _ := n1
    _ = (2 / gg D) ^ ((s - 1) * D.R.k * D.R.f) *
          ((D.R.k : ℝ) * D.host.v / (Real.exp 1 * Real.pi)) ^ (D.R.k * D.R.f) *
          (XiS D u (HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y) c s *
            ((HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y) ^ pairCountExponent D c s * (c * s * D.R.f) ^ (6 * s * D.R.f)) *
            Real.sqrt (rows_l D large₂ c C2 Ch q x * rows_l D large₂ c C2 Ch q y)) * ((1 + δ) * rDD D u') := by ring
    _ ≤ (2 / gg D) ^ ((s - 1) * D.R.k * D.R.f) *
          ((D.R.k : ℝ) * D.host.v / (Real.exp 1 * Real.pi)) ^ (D.R.k * D.R.f) *
          (XiS D u (rows_P D large₂ c Ch ^ 2) c s * ((rows_P D large₂ c Ch ^ pairCountExponent D c s) ^ 2 *
            (rows_P D large₂ c Ch ^ (c * (D.R.rS : ℝ) ^ 2)) ^ 2 * (c * s * D.R.f) ^ (6 * s * D.R.f) * GamS D large₂) *
            (sizeZ D large₂.sc.b Ch x ^ (-(12 * ((D.R.rS : ℝ) + 1) ^ 2)) *
              sizeZ D large₂.sc.b Ch y ^ (-(12 * ((D.R.rS : ℝ) + 1) ^ 2)))) * ((1 + δ) * rDD D u') :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left n2 hA0) hτ0
    _ = _ := by unfold rows_R; ring

theorem rows_nd_size (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q) (𝒵 : Finset (GramM D))
    (h𝒵 : ∀ Z ∈ 𝒵, wordPairGramGood X u u' large₂ c Z) :
    ∑ Z ∈ 𝒵, sizeZ D large₂.sc.b Ch Z ^ (-(12 * ((D.R.rS : ℝ) + 1) ^ 2)) ≤ rows_Phi D large₂ c Ch := by
  have hrd := d_rdE_pos h.hH.1
  have hb2 := d_two_le_b D large₂
  refine rows_sizeSum X h.hE hrd (rows_f_pos D) 𝒵 (fun Z => sizeZ D large₂.sc.b Ch Z) (fun Z _ => rows_one_le_sizeZ _ _ _)
    (rows_P D large₂ c Ch) (rows_P_one_le D large₂ c Ch) ?_ ?_ _ le_rfl
  · intro Z hZ; obtain ⟨t, hG, hr, hEq, _⟩ := h𝒵 Z hZ; exact ⟨t, hG, hr, hEq⟩
  · intro Z hZ j I J hdet
    obtain ⟨t, hG, hr, hEq, hred⟩ := h𝒵 Z hZ
    refine (hred j I J hdet).trans ?_
    rw [← rows_HHZ_inv hEq]
    exact rows_HHZ_cmp hrd (by linarith) c Ch Z

theorem rows_R_nonneg (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q) (s : ℕ) :
    0 ≤ rows_R D large₂ u u' c Ch δ s := by
  have hg2 := two_le_gg_of_count_hypotheses h.hH.1
  have hv1 : 1 ≤ D.host.v := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h19, _⟩ := h.hH.1.1
    exact h19
  have hP1 := rows_P_one_le D large₂ c Ch
  have hτ0 : 0 ≤ (1 + δ) * rDD D u' := mul_nonneg (by linarith [h.hδ]) (rows_rDD_nonneg D u')
  have hGam0 : 0 < GamS D large₂ := by unfold GamS; exact Real.exp_pos _
  have hXiP0 : 0 ≤ XiS D u (rows_P D large₂ c Ch ^ 2) c s := rows_XiS_nonneg D u (by positivity) h.hc s
  have hpi := Real.pi_pos
  have : 0 ≤ gg D := by linarith
  have : 0 ≤ D.host.v := by linarith
  have := h.hc
  unfold rows_R
  positivity

theorem rows_wP_sum (hdim : 0 < dimPi (hc := D.hcW) u) (S : Finset (D.s.Pair u u')) :
    ∑ p ∈ S, wP X p = dimPi (hc := D.hcW) u * ∑ p ∈ S, X.wRow p *
      (aT X (D.s.pfst p) / Real.sqrt (dimPi (hc := D.hcW) u) * (aT X (D.s.psnd p) / Real.sqrt (dimPi (hc := D.hcW) u))) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold wP
  have hs2 : Real.sqrt (dimPi (hc := D.hcW) u) * Real.sqrt (dimPi (hc := D.hcW) u) = dimPi (hc := D.hcW) u :=
    Real.mul_self_sqrt hdim.le
  have hs0 : Real.sqrt (dimPi (hc := D.hcW) u) ≠ 0 := (Real.sqrt_pos.2 hdim).ne'
  calc X.wRow p * (aT X (D.s.pfst p) * aT X (D.s.psnd p))
      = (Real.sqrt (dimPi (hc := D.hcW) u) * Real.sqrt (dimPi (hc := D.hcW) u)) * (X.wRow p *
          (aT X (D.s.pfst p) / Real.sqrt (dimPi (hc := D.hcW) u) *
            (aT X (D.s.psnd p) / Real.sqrt (dimPi (hc := D.hcW) u)))) := by field_simp
    _ = _ := by rw [hs2]

theorem rows_ND_record (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q)
    (s : ℕ) (hs : 2 ≤ s) (hsk : s ≤ D.R.k)
    (hq2 : 4 * (c * D.R.k) + 4 * pairCountExponent D c s + 4 * (c * (D.R.rS : ℝ) ^ 2) + C2 * (D.R.m : ℝ) ^ 2 / 2 +
      12 * ((D.R.rS : ℝ) + 1) ^ 2 ≤ (q : ℝ) / ((D.R.rS : ℝ) + 1)) :
    RowBound X Y (clsND X s) (rows_ndB D large₂ u u' c Ch δ s) := by
  refine rowBound_relevant Y (fun p hp => ⟨hp.1, hp.2.1⟩) ?_
  intro S hS
  have sp1 : ∀ p ∈ S, ZEquiv (termGramMatrix X (D.s.pfst p)) (termReducedGramMatrix Y h.hH h.hHH (D.s.pfst p)) ∧
      wordPairGramGood X u u' large₂ c (termReducedGramMatrix Y h.hH h.hHH (D.s.pfst p)) := fun p hp =>
    rows_Zr_spec Y h.hH h.hHH _ (hS p hp).1.1 (hS p hp).2.1
  have sp2 : ∀ p ∈ S, ZEquiv (termGramMatrix X (D.s.psnd p)) (termReducedGramMatrix Y h.hH h.hHH (D.s.psnd p)) ∧
      wordPairGramGood X u u' large₂ c (termReducedGramMatrix Y h.hH h.hHH (D.s.psnd p)) := fun p hp =>
    rows_Zr_spec Y h.hH h.hHH _ (hS p hp).1.2.1 (hS p hp).2.2
  have key := weighted_sum_le' S (fun p => X.wRow p) (fun p => aT X (D.s.pfst p) / Real.sqrt (dimPi (hc := D.hcW) u))
    (fun p => aT X (D.s.psnd p) / Real.sqrt (dimPi (hc := D.hcW) u)) (fun p => termReducedGramMatrix Y h.hH h.hHH (D.s.pfst p))
    (fun p => termReducedGramMatrix Y h.hH h.hHH (D.s.psnd p)) (massRows D Y.F0 Y.what₂) (rows_R D large₂ u u' c Ch δ s)
    (rows_Phi D large₂ c Ch) (fun x y => wordSublatticeTripleBound D large₂ u c x y s (rows_DeZ D u u' s x y))
    (rows_al D large₂ u u' c C2 Ch δ q) (fun Z => sizeZ D large₂.sc.b Ch Z ^ (-(12 * ((D.R.rS : ℝ) + 1) ^ 2)))
    (rows_massRows_nonneg Y) (rows_R_nonneg Y h s)
    (fun p _ => (X.wRow_pos p).le) (fun p _ => div_nonneg (aT_nonneg _ _) (Real.sqrt_nonneg _))
    (fun p _ => div_nonneg (aT_nonneg _ _) (Real.sqrt_nonneg _))
    (fun p hp => rows_nd_term Y h _ (hS p hp).1.1 (hS p hp).2.1)
    (fun p hp => rows_nd_term Y h _ (hS p hp).1.2.1 (hS p hp).2.2)
    (by
      rintro x y ⟨p1, hp1, rfl⟩ ⟨p2, hp2, rfl⟩ S' hS' hl
      refine rows_nd_count Y h s hs hsk _ _ (sp1 p1 hp1).2 (sp2 p2 hp2).2 S' fun p hp => ?_
      refine ⟨(hS p (hS' hp)).1, ?_, ?_⟩
      · rw [← (hl p hp).1]; exact (sp1 p (hS' hp)).1
      · rw [← (hl p hp).2]; exact (sp2 p (hS' hp)).1)
    (by
      rintro x y ⟨p1, hp1, rfl⟩ ⟨p2, hp2, rfl⟩
      exact rows_nd_prod Y h s hs hq2 _ _ (sp1 p1 hp1).2 (sp2 p2 hp2).2)
    (fun x => Real.sqrt_nonneg _)
    (fun x => Real.rpow_nonneg (le_trans zero_le_one (rows_one_le_sizeZ _ _ _)) _)
    (fun 𝒵 h𝒵 => rows_nd_size Y h 𝒵 fun Z hZ => by obtain ⟨p, hp, rfl⟩ := h𝒵 Z hZ; exact (sp1 p hp).2)
    (fun 𝒵 h𝒵 => rows_nd_size Y h 𝒵 fun Z hZ => by obtain ⟨p, hp, rfl⟩ := h𝒵 Z hZ; exact (sp2 p hp).2)
  rw [rows_wP_sum h.hdim S]
  calc dimPi (hc := D.hcW) u * _
      ≤ dimPi (hc := D.hcW) u * (massRows D Y.F0 Y.what₂ * (rows_R D large₂ u u' c Ch δ s * rows_Phi D large₂ c Ch ^ 2)) :=
        mul_le_mul_of_nonneg_left key h.hdim.le
    _ = massRows D Y.F0 Y.what₂ * dimPi (hc := D.hcW) u * rows_ndB D large₂ u u' c Ch δ s := by
        unfold rows_ndB; ring

end ND

end Formalism.MainNotions.BridgeLemma₂

end
