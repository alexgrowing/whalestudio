import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FamRaise
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsFinal
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsAll

noncomputable section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma Formalism.MainNotions.BridgeLemma₂

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Formalism.L2.SG.RowsU

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure UC where
  c3 : ℝ
  cH : ℝ
  cV : ℝ
  cS : ℝ
  c4 : ℝ
  CaF : ℝ → ℝ
  secondOrderBound : ℝ → ℝ
  ChF : ℝ → ℝ

def c0ND (CT A C0 : ℝ) (U : UC) : ℝ :=
  let c := max (max U.c3 1) (max (|U.cH| + 2) (|U.cV| + 2))
  max c (4 + (c ^ 2 + 2 * max (U.ChF (9 * c + 3) - c) 0) * (6 * c + 2))

def degenerateConstant (CT : ℝ) (U : UC) : ℝ :=
  let c := max (max (max U.c3 (max (max 1 CT) (|U.cH| + 2))) 1) (max (|U.cH| + 2) (|U.cV| + 2))
  max (max c (4 + (c ^ 2 + 2 * max (U.ChF (9 * c + 3) - c) 0) * (6 * c + 2)))
    (max (2 * U.secondOrderBound (9 * c + 3)) |U.CaF (9 * c + 3)|)

def corankOneConstant (CT A C0 CGam : ℝ) (U : UC) : ℝ :=
  let c := max (max U.c3 1) (max (max (|U.cH| + 2) (|U.cV| + 2)) (max (|U.cS| + 2) (|U.c4| + 2)))
  max (max (4 * Real.sqrt A) (2 * Real.sqrt (2 * C0) * c))
    (max (CGam + U.secondOrderBound (9 * c + 3)) (4 + 2 * (c ^ 2 + 2 * max (U.ChF (9 * c + 3) - c) 0) * (c + 1)))

section Fam

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1)
  (Cg cb Cu cT CT C0 A : ℝ)

def UAdm (U : UC) : Prop :=
  (∀ C ≥ U.c3, OwnEv Fm fun C' Cl x i => ∀ u u',
    VanishingOnXAndXPlus.adm20 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A 3 C) ∧
  (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.HerrCocycleExtensionClass (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A U.cH) ∧
  (OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u',
    VanishingOnXAndXPlus.TermVolumeSmallCellBound (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1 (Y x hx i u u') C' Cl Cg cb Cu cT CT C0 A U.cV) ∧
  (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.ArchimedeanSignatureMatching (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A U.cS) ∧
  (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.adm21 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A U.c4) ∧
  ∀ Cpr : ℝ, 0 ≤ U.ChF Cpr ∧ 0 ≤ U.CaF Cpr ∧ ∀ δ > 0, OwnEv Fm fun C' Cl x i =>
    VanishingOnXAndXPlus.AmplitudeBoundsConjunction (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1 Cpr (U.CaF Cpr) (U.secondOrderBound Cpr) (U.ChF Cpr) δ

theorem rowsKBU (U : UC) (hU : UAdm Fm C1 X Y Cg cb Cu cT CT C0 A U) :
    ∀ c ≥ max (max 1 CT) (|U.cH| + 2), OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u',
      Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A → rows_KBound (Y x hx i u u') c := by
  intro c hc
  obtain ⟨_, h27, _⟩ := hU
  refine OwnEv.mono ?_ h27
  intro C' Cl x i h hx u u' hH
  have hc1 : 1 ≤ c := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hc
  have hCT : CT ≤ c := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hc
  have hcH : |U.cH| + 2 ≤ c := le_trans (le_max_right _ _) hc
  exact rows_KBound_of (Y x hx i u u') hH (rows_stHH_mono (by linarith [le_abs_self U.cH])
    (by linarith [neg_abs_le U.cH]) (h u u')) hc1 hCT

theorem rowsNDU (hAdm : VanishingOnXAndXPlus.AdmF Fm C1 X Y) (hT : rows_TiesF Fm C1 X Y) (U : UC)
    (hU : UAdm Fm C1 X Y Cg cb Cu cT CT C0 A U) :
    ∀ C ≥ c0ND CT A C0 U, OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u',
      Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A → RowsND (X x hx i) (Y x hx i u u') C := by
  intro C hC
  simp only [c0ND] at hC
  obtain ⟨_, _, _, _, _, _, _, h10a, _, _, _, h14, _, _, _, _, hall⟩ := hAdm
  obtain ⟨_, _, _, _, _, _, _, _, h6, _, h8, _, h10b, _, _, h20, _, _, h27, hVol⟩ := hall Cg cb Cu cT CT C0 A
  set c3 := U.c3 with hc3def
  have LocalHeightDeterminant := hU.1
  set cH := U.cH with hcHdef
  obtain ⟨x27, H27⟩ := hU.2.1
  set cV := U.cV with hcVdef
  obtain ⟨xV, HV⟩ := hU.2.2.1
  set c : ℝ := max (max c3 1) (max (|cH| + 2) (|cV| + 2)) with hcdef
  have k1 : c3 ≤ c := by rw [hcdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have k2 : 1 ≤ c := by rw [hcdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have k3 : |cH| + 2 ≤ c := by rw [hcdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have k4 : |cV| + 2 ≤ c := by rw [hcdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨x20, H20x⟩ := LocalHeightDeterminant c k1
  obtain ⟨hCh, _, HA⟩ := hU.2.2.2.2.2 (9 * c + 3)
  set Ca := U.CaF (9 * c + 3) with hCadef
  set C2 := U.secondOrderBound (9 * c + 3) with hC2def
  set Ch := U.ChF (9 * c + 3) with hChdef
  obtain ⟨xA, HAx⟩ := HA 1 one_pos
  obtain ⟨x6, H6⟩ := h6 1 one_pos
  obtain ⟨x8, H8⟩ := h8
  obtain ⟨x10, H10⟩ := h10b
  obtain ⟨xk, _, Hk⟩ := ev_kLow Fm |C2|
  refine ownEv_intro Fm (max (max (max x20 x27) (max xV xA)) (max (max x6 x8) (max x10 xk)))
    fun x hx _ i hx1 u u' hH => ?_
  have g20 : x20 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have g27 : x27 ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have gV : xV ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hx
  have gA : xA ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hx
  have g6 : x6 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have g8 : x8 ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have g10 : x10 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  have gk : xk ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  have hc0 : 0 ≤ c := by linarith
  have hcC : c ≤ C := le_trans (le_max_left _ _) hC
  have hC1 : 1 ≤ C := k2.trans hcC
  have hCsq : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C ^ 2 := by
    have := le_trans (le_max_right _ _) hC
    nlinarith
  have hr0 : (0 : ℝ) ≤ (Fm.D x i).R.rS := by positivity
  have hm2 : (2 : ℝ) ≤ (Fm.D x i).R.m := by rw [rows_m_cast]; linarith
  have hf1 : (1 : ℝ) ≤ (Fm.D x i).R.f := by exact_mod_cast rows_f_pos (Fm.D x i)
  have hL1 := d_one_le_L (Fm.D x i) (Fm.L x i)
  have hkm : ((Fm.D x i).R.m : ℝ) + 3 ≤ (Fm.D x i).R.k := by exact_mod_cast (Fm.D x i).R.m_add_three_le_k
  have ha2 : |C2| * ((Fm.D x i).R.m : ℝ) ^ 2 ≤ (Fm.D x i).R.k := by
    refine le_trans ?_ (Hk x gk i)
    have e1 : ((Fm.D x i).R.m : ℝ) ^ 2 ≤ ((Fm.D x i).R.m : ℝ) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have e2 : ((Fm.D x i).R.m : ℝ) ^ 5 ≤ ((Fm.D x i).R.m : ℝ) ^ 5 * (Fm.D x i).R.f * (Fm.L x i).sc.L := by
      have h5 : 0 ≤ ((Fm.D x i).R.m : ℝ) ^ 5 := by positivity
      nlinarith [mul_nonneg h5 (by linarith : 0 ≤ ((Fm.D x i).R.f : ℝ) - 1),
        mul_nonneg (mul_nonneg h5 (by linarith : 0 ≤ ((Fm.D x i).R.f : ℝ))) (by linarith : 0 ≤ (Fm.L x i).sc.L - 1)]
    calc |C2| * ((Fm.D x i).R.m : ℝ) ^ 2 ≤ |C2| * (((Fm.D x i).R.m : ℝ) ^ 5 * (Fm.D x i).R.f * (Fm.L x i).sc.L) :=
          mul_le_mul_of_nonneg_left (e1.trans e2) (abs_nonneg _)
      _ = |C2| * ((Fm.D x i).R.m : ℝ) ^ 5 * (Fm.D x i).R.f * (Fm.L x i).sc.L := by ring
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = 4 * (c * (Fm.D x i).R.k) + 4 * pairCountExponent (Fm.D x i) c (Fm.D x i).R.k +
    4 * (c * ((Fm.D x i).R.rS : ℝ) ^ 2) + |C2| * ((Fm.D x i).R.m : ℝ) ^ 2 / 2 + 12 * (((Fm.D x i).R.rS : ℝ) + 1) ^ 2 := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by
    rw [hadef]
    have := pairCountExponent_nonneg (Fm.D x i) hc0 (Fm.D x i).R.k
    positivity
  have hqb := rows_q_bound (m := (Fm.D x i).R.m) (k := (Fm.D x i).R.k) (r := (Fm.D x i).R.rS) (c := c)
    (cf := cF (Fm.D x i).R.f) (a2 := |C2| * ((Fm.D x i).R.m : ℝ) ^ 2) (rows_m_cast _) hr0 hkm hc0 (rows_cF_le hH) ha2
  have hqb' : (((Fm.D x i).R.rS : ℝ) + 1) * a + 1 ≤ (9 * c + 3) * (Fm.D x i).R.k * ((Fm.D x i).R.m : ℝ) ^ 2 := by
    rw [hadef]; unfold pairCountExponent; exact hqb
  have hra0 : 0 ≤ (((Fm.D x i).R.rS : ℝ) + 1) * a := by positivity
  have hyp : rows_Hyps (Y x hx1 i u u') (sC' Fm) (sCl Fm) Cg cb Cu cT CT C0 A c (9 * c + 3) Ca C2 Ch 1 1
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
      hδ := zero_le_one
      hThA := h14 x i u u'
      hT := (hT x hx1 i u u').1
      hG0 := (hT x hx1 i u u').2.1
      hE := (hT x hx1 i u u').2.2
      hc := hc0
      hCh := hCh
      hdim := rows_dim_pos (Y x hx1 i u u') hH.1 (H8 x g8 i u u' hH)
      hq := by linarith [(Nat.ceil_lt_add_one hra0).le] }
  refine rows_RowsND_record _ hyp le_rfl hcC hC1 hCsq ?_
  rw [le_div_iff₀ (by positivity)]
  have h1 := Nat.le_ceil ((((Fm.D x i).R.rS : ℝ) + 1) * a)
  have h2 : C2 * ((Fm.D x i).R.m : ℝ) ^ 2 / 2 ≤ |C2| * ((Fm.D x i).R.m : ℝ) ^ 2 / 2 := by
    have := le_abs_self C2
    gcongr
  calc _ ≤ a * (((Fm.D x i).R.rS : ℝ) + 1) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hadef]; linarith
    _ = (((Fm.D x i).R.rS : ℝ) + 1) * a := by ring
    _ ≤ _ := h1

theorem rowsDegU (hAdm : VanishingOnXAndXPlus.AdmF Fm C1 X Y) (hT : rows_TiesF Fm C1 X Y) (U : UC)
    (hU : UAdm Fm C1 X Y Cg cb Cu cT CT C0 A U) :
    ∀ C ≥ degenerateConstant CT U, OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u',
      Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A → RowsDeg (X x hx i) (Y x hx i u u') C := by
  intro C hC
  simp only [degenerateConstant] at hC
  obtain ⟨_, _, _, _, _, _, _, h10a, _, _, _, h14, _, _, _, _, hall⟩ := hAdm
  obtain ⟨_, _, _, _, _, _, _, _, h6, _, h8, _, h10b, _, _, h20, _, _, h27, hVol⟩ := hall Cg cb Cu cT CT C0 A
  set c3 := U.c3 with hc3def
  have LocalHeightDeterminant := hU.1
  set cH := U.cH with hcHdef
  obtain ⟨x27, H27⟩ := hU.2.1
  set cV := U.cV with hcVdef
  obtain ⟨xV, HV⟩ := hU.2.2.1
  set cK := max (max 1 CT) (|cH| + 2) with hcKdef
  have HK := rowsKBU Fm C1 X Y Cg cb Cu cT CT C0 A U hU
  set c : ℝ := max (max (max c3 cK) 1) (max (|cH| + 2) (|cV| + 2)) with hcdef
  have k1 : c3 ≤ c := by rw [hcdef]; exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have k5 : cK ≤ c := by rw [hcdef]; exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have k2 : 1 ≤ c := by rw [hcdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have k3 : |cH| + 2 ≤ c := by rw [hcdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have k4 : |cV| + 2 ≤ c := by rw [hcdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨x20, H20x⟩ := LocalHeightDeterminant c k1
  obtain ⟨xK, HKx⟩ := HK c k5
  obtain ⟨hCh, _, HA⟩ := hU.2.2.2.2.2 (9 * c + 3)
  set Ca := U.CaF (9 * c + 3) with hCadef
  set C2 := U.secondOrderBound (9 * c + 3) with hC2def
  set Ch := U.ChF (9 * c + 3) with hChdef
  obtain ⟨xA, HAx⟩ := HA 1 one_pos
  obtain ⟨x6, H6⟩ := h6 1 one_pos
  obtain ⟨x8, H8⟩ := h8
  obtain ⟨x10, H10⟩ := h10b
  obtain ⟨xk, _, Hk⟩ := ev_kLow Fm (3 * |C2|)
  refine ownEv_intro Fm (max (max (max (max x20 xK) x27) (max xV xA)) (max (max x6 x8) (max x10 xk)))
    fun x hx _ i hx1 u u' hH => ?_
  have g20 : x20 ≤ x := le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _))
    (le_max_left _ _)) hx
  have gK : xK ≤ x := le_trans (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _))
    (le_max_left _ _)) hx
  have g27 : x27 ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have gV : xV ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hx
  have gA : xA ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hx
  have g6 : x6 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have g8 : x8 ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have g10 : x10 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  have gk : xk ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  have hc0 : 0 ≤ c := by linarith
  have hcC : c ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hC
  have hC1 : 1 ≤ C := k2.trans hcC
  have hCsq : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C ^ 2 := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC
    nlinarith
  have hC2 : 2 * C2 ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC
  have hCa : |Ca| ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC
  have hr0 : (0 : ℝ) ≤ (Fm.D x i).R.rS := by positivity
  have hm2 : (2 : ℝ) ≤ (Fm.D x i).R.m := by rw [rows_m_cast]; linarith
  have hf1 : (1 : ℝ) ≤ (Fm.D x i).R.f := by exact_mod_cast rows_f_pos (Fm.D x i)
  have hL1 := d_one_le_L (Fm.D x i) (Fm.L x i)
  have hkm : ((Fm.D x i).R.m : ℝ) + 3 ≤ (Fm.D x i).R.k := by exact_mod_cast (Fm.D x i).R.m_add_three_le_k
  have ha2 : |C2| * ((Fm.D x i).R.m : ℝ) ^ 2 + |C2| * ((Fm.D x i).R.m : ℝ) ^ 4 * 2 ≤ (Fm.D x i).R.k := by
    refine le_trans ?_ (Hk x gk i)
    have e1 : ((Fm.D x i).R.m : ℝ) ^ 2 ≤ ((Fm.D x i).R.m : ℝ) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have e4 : ((Fm.D x i).R.m : ℝ) ^ 4 ≤ ((Fm.D x i).R.m : ℝ) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have e2 : ((Fm.D x i).R.m : ℝ) ^ 5 ≤ ((Fm.D x i).R.m : ℝ) ^ 5 * (Fm.D x i).R.f * (Fm.L x i).sc.L := by
      have h5 : 0 ≤ ((Fm.D x i).R.m : ℝ) ^ 5 := by positivity
      nlinarith [mul_nonneg h5 (by linarith : 0 ≤ ((Fm.D x i).R.f : ℝ) - 1),
        mul_nonneg (mul_nonneg h5 (by linarith : 0 ≤ ((Fm.D x i).R.f : ℝ))) (by linarith : 0 ≤ (Fm.L x i).sc.L - 1)]
    have hab := abs_nonneg C2
    calc |C2| * ((Fm.D x i).R.m : ℝ) ^ 2 + |C2| * ((Fm.D x i).R.m : ℝ) ^ 4 * 2
        = |C2| * (((Fm.D x i).R.m : ℝ) ^ 2 + 2 * ((Fm.D x i).R.m : ℝ) ^ 4) := by ring
      _ ≤ |C2| * (3 * (((Fm.D x i).R.m : ℝ) ^ 5 * (Fm.D x i).R.f * (Fm.L x i).sc.L)) :=
          mul_le_mul_of_nonneg_left (by linarith) hab
      _ = 3 * |C2| * ((Fm.D x i).R.m : ℝ) ^ 5 * (Fm.D x i).R.f * (Fm.L x i).sc.L := by ring
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = 4 * (c * (Fm.D x i).R.k) + 4 * pairCountExponent (Fm.D x i) c (Fm.D x i).R.k +
    4 * (c * ((Fm.D x i).R.rS : ℝ) ^ 2) + (|C2| * ((Fm.D x i).R.m : ℝ) ^ 2 + |C2| * ((Fm.D x i).R.m : ℝ) ^ 4 * 2) / 2 +
    12 * (((Fm.D x i).R.rS : ℝ) + 1) ^ 2 := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by
    rw [hadef]
    have := pairCountExponent_nonneg (Fm.D x i) hc0 (Fm.D x i).R.k
    positivity
  have hqb := rows_q_bound (m := (Fm.D x i).R.m) (k := (Fm.D x i).R.k) (r := (Fm.D x i).R.rS) (c := c)
    (cf := cF (Fm.D x i).R.f) (a2 := |C2| * ((Fm.D x i).R.m : ℝ) ^ 2 + |C2| * ((Fm.D x i).R.m : ℝ) ^ 4 * 2)
    (rows_m_cast _) hr0 hkm hc0 (rows_cF_le hH) ha2
  have hqb' : (((Fm.D x i).R.rS : ℝ) + 1) * a + 1 ≤ (9 * c + 3) * (Fm.D x i).R.k * ((Fm.D x i).R.m : ℝ) ^ 2 := by
    rw [hadef]; unfold pairCountExponent; exact hqb
  have hra0 : 0 ≤ (((Fm.D x i).R.rS : ℝ) + 1) * a := by positivity
  have hyp : rows_Hyps (Y x hx1 i u u') (sC' Fm) (sCl Fm) Cg cb Cu cT CT C0 A c (9 * c + 3) Ca C2 Ch 1 1
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
      hδ := zero_le_one
      hThA := h14 x i u u'
      hT := (hT x hx1 i u u').1
      hG0 := (hT x hx1 i u u').2.1
      hE := (hT x hx1 i u u').2.2
      hc := hc0
      hCh := hCh
      hdim := rows_dim_pos (Y x hx1 i u u') hH.1 (H8 x g8 i u u' hH)
      hq := by linarith [(Nat.ceil_lt_add_one hra0).le] }
  refine rows_RowsDeg_record _ hyp (HKx x gK i hx1 u u' hH) k2 hcC hC1 hCsq hC2 hCa ?_
  rw [le_div_iff₀ (by positivity)]
  have h1 := Nat.le_ceil ((((Fm.D x i).R.rS : ℝ) + 1) * a)
  have h2 : (C2 * ((Fm.D x i).R.m : ℝ) ^ 2 + C2 * ((Fm.D x i).R.m : ℝ) ^ 4 * 2) / 2 ≤
      (|C2| * ((Fm.D x i).R.m : ℝ) ^ 2 + |C2| * ((Fm.D x i).R.m : ℝ) ^ 4 * 2) / 2 := by
    have := le_abs_self C2
    gcongr
  calc _ ≤ a * (((Fm.D x i).R.rS : ℝ) + 1) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hadef]; linarith
    _ = (((Fm.D x i).R.rS : ℝ) + 1) * a := by ring
    _ ≤ _ := h1

theorem rowsOneU (hAdm : VanishingOnXAndXPlus.AdmF Fm C1 X Y) (hT : rows_TiesF Fm C1 X Y)
    (hTI : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), wordPairTermInjective (X x hx i) (Y x hx i u u'))
    (hBL : ∀ x (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), wordPairBetaLattice (Fm.D x i) u u') (U : UC)
    (hU : UAdm Fm C1 X Y Cg cb Cu cT CT C0 A U) :
    ∀ C ≥ corankOneConstant CT A C0 Fm.CGam U, OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u',
      Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A → RowsOne (X x hx i) (Y x hx i u u') C := by
  intro C hC
  simp only [corankOneConstant] at hC
  obtain ⟨_, _, _, _, _, _, _, h10a, _, _, _, h14, _, _, _, _, hall⟩ := hAdm
  obtain ⟨_, _, _, _, _, _, _, h4, h6, h7, h8, _, h10b, _, _, h20, h21, _, h27, hVol⟩ := hall Cg cb Cu cT CT C0 A
  set c3 := U.c3 with hc3def
  have LocalHeightDeterminant := hU.1
  set cH := U.cH with hcHdef
  obtain ⟨x27, H27⟩ := hU.2.1
  set cV := U.cV with hcVdef
  obtain ⟨xV, HV⟩ := hU.2.2.1
  set cS := U.cS with hcSdef
  obtain ⟨x4, H4⟩ := hU.2.2.2.1
  set c4 := U.c4 with hc4def
  obtain ⟨x21, H21⟩ := hU.2.2.2.2.1
  set c : ℝ := max (max c3 1) (max (max (|cH| + 2) (|cV| + 2)) (max (|cS| + 2) (|c4| + 2))) with hcdef
  have k1 : c3 ≤ c := by rw [hcdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have k2 : 1 ≤ c := by rw [hcdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have k3 : |cH| + 2 ≤ c := by rw [hcdef]; exact le_trans (le_max_four _ _ _ _).1 (le_max_right _ _)
  have k4 : |cV| + 2 ≤ c := by rw [hcdef]; exact le_trans (le_max_four _ _ _ _).2.1 (le_max_right _ _)
  have k5 : |cS| + 2 ≤ c := by rw [hcdef]; exact le_trans (le_max_four _ _ _ _).2.2.1 (le_max_right _ _)
  have k6 : |c4| + 2 ≤ c := by rw [hcdef]; exact le_trans (le_max_four _ _ _ _).2.2.2 (le_max_right _ _)
  obtain ⟨x20, H20x⟩ := LocalHeightDeterminant c k1
  obtain ⟨hCh, hCa, HA⟩ := hU.2.2.2.2.2 (9 * c + 3)
  set Ca := U.CaF (9 * c + 3) with hCadef
  set C2 := U.secondOrderBound (9 * c + 3) with hC2def
  set Ch := U.ChF (9 * c + 3) with hChdef
  obtain ⟨xA, HAx⟩ := HA (1 / 4) (by norm_num)
  obtain ⟨x6, H6⟩ := h6 (1 / 2) (by norm_num)
  obtain ⟨x7, H7⟩ := h7
  obtain ⟨x8, H8⟩ := h8
  obtain ⟨x10, H10⟩ := h10b
  obtain ⟨xk, _, Hk⟩ := ev_kLow Fm |C2|
  obtain ⟨xc, _, Hc⟩ := ev_k Fm ((max Ca 1) ^ 3)
  clear hc3def hcHdef hcVdef hcSdef hc4def hCadef hC2def hChdef hU
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

def c0U (CT A C0 CGam : ℝ) (U : UC) : ℝ := max (c0ND CT A C0 U) (max (degenerateConstant CT U) (corankOneConstant CT A C0 CGam U))

theorem rowsFU (hAdm : VanishingOnXAndXPlus.AdmF Fm C1 X Y) (hT : rows_TiesF Fm C1 X Y)
    (hTI : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), wordPairTermInjective (X x hx i) (Y x hx i u u'))
    (hBL : ∀ x (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), wordPairBetaLattice (Fm.D x i) u u') (U : UC)
    (hU : UAdm Fm C1 X Y Cg cb Cu cT CT C0 A U) :
    ∀ C ≥ c0U CT A C0 Fm.CGam U, OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u',
      Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A →
        RowsND (X x hx i) (Y x hx i u u') C ∧ RowsDeg (X x hx i) (Y x hx i u u') C ∧
          RowsOne (X x hx i) (Y x hx i u u') C := by
  intro C hC
  have h1 := rowsNDU Fm C1 X Y Cg cb Cu cT CT C0 A hAdm hT U hU C (le_trans (le_max_left _ _) hC)
  have h2 := rowsDegU Fm C1 X Y Cg cb Cu cT CT C0 A hAdm hT U hU C
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC)
  have h3 := rowsOneU Fm C1 X Y Cg cb Cu cT CT C0 A hAdm hT hTI hBL U hU C
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC)
  refine OwnEv.mono ?_ ((h1.and h2).and h3)
  rintro C' Cl x i ⟨⟨a, b⟩, c⟩ hx u u' hH
  exact ⟨a hx u u' hH, b hx u u' hH, c hx u u' hH⟩

end Fam

end Formalism.L2.SG.RowsU
