import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.AdmBoundsBOfAdm
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LogbHBNonneg
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LenQuotSpanNeTopDvr
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsLiftFLeSgOfThick
import Formalism.SharpRestriction.LevelLetterCocycles.StatementFamilies.ArcLiftingSetup
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

def C0 : ℝ := 320

section Num

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]

theorem colLeR_mono {PD : PeriodData G Qp K₀ K B BdR} {T₁ T₂ : LocLat G Qp LL O}
    {F : LatHom T₁.L T₂.L} {x y : ℝ} (h : TruncatedSeriesCountingBounds.ColLeR PD F x) (hxy : x ≤ y) : TruncatedSeriesCountingBounds.ColLeR PD F y := by
  obtain ⟨mm, k, h1, h2, h3⟩ := h
  exact ⟨mm, k, h1, h2, h3.trans (mul_le_mul_of_nonneg_right hxy (Nat.cast_nonneg k))⟩

end Num

theorem logb_two_mul_nonneg (l h : ℕ) (hl : 2 ≤ l) : 0 ≤ Real.logb l (2 * (h : ℝ)) := by
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · simp
  · apply Real.logb_nonneg
    · exact_mod_cast (show 1 < l by omega)
    · have : (1 : ℝ) ≤ h := by exact_mod_cast hpos
      linarith

theorem sg_le_alt {n : ℕ} (l b w S η : ℕ) (size : ZMod n → ℕ) (bd : ℝ) (hl : 2 ≤ l) (hbd : 0 ≤ bd) :
    Sg l b w S η size ≤ (TruncatedSeriesCountingBounds.hB b w S η size : ℝ) / (l : ℝ) ^ 2 + ((w : ℝ) + η) / l + S + 1 +
      Real.logb l (2 * (TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) + η * bd := by
  unfold Sg
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast (show 1 ≤ l by omega)
  have h1 : ((w : ℝ) + S + η) / l = ((w : ℝ) + η) / l + (S : ℝ) / l := by ring
  have h2 : (S : ℝ) / l ≤ S := div_le_self (Nat.cast_nonneg S) hl'
  have h3 : 0 ≤ (η : ℝ) * bd := mul_nonneg (Nat.cast_nonneg η) hbd
  linarith

section Record

variable (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)

theorem arith_alt {C N r m e z e' a b' S lg η bd Sgv : ℝ} (hC : 320 ≤ C) (hN : 0 ≤ N) (hr : 0 ≤ r)
    (hm : 0 ≤ m) (he' : 0 ≤ e') (ha : 0 ≤ a) (hb' : 0 ≤ b') (hS : 0 ≤ S) (hlg : 0 ≤ lg) (hη : 0 ≤ η)
    (hbd : 0 ≤ bd) (hSg : Sgv ≤ a + b' + S + 1 + lg) (he : e ≤ 55 * Sgv + 13 * S + η * bd)
    (hz : z ≤ 4 * N * m) :
    (N + 1) * r * e + z * e' ≤ C * (N + 1) * r * (a + b' + S + 1 + lg + η * bd) + C * N * m * e' := by
  have hX : e ≤ C * (a + b' + S + 1 + lg + η * bd) := by
    have h1 : 0 ≤ η * bd := mul_nonneg hη hbd
    have h2 : e ≤ 69 * (a + b' + S + 1 + lg + η * bd) := by nlinarith
    have h3 : 0 ≤ a + b' + S + 1 + lg + η * bd := by linarith
    nlinarith
  have hNr : 0 ≤ (N + 1) * r := by positivity
  have h4 : (N + 1) * r * e ≤ (N + 1) * r * (C * (a + b' + S + 1 + lg + η * bd)) :=
    mul_le_mul_of_nonneg_left hX hNr
  have hNm : 0 ≤ N * m := mul_nonneg hN hm
  have h5 : z * e' ≤ C * N * m * e' := by
    have : z ≤ C * N * m := by nlinarith
    exact mul_le_mul_of_nonneg_right this he'
  nlinarith

theorem arith_big {C N r m e₀ e' a b' S lg η bd Sgv : ℝ} (hC : 320 ≤ C) (hN : 0 ≤ N) (hr : 0 ≤ r)
    (hm : 0 ≤ m) (he' : 0 ≤ e') (ha : 0 ≤ a) (hb' : 0 ≤ b') (hS : 0 ≤ S) (hlg : 0 ≤ lg) (hη : 0 ≤ η)
    (hbd : 0 ≤ bd) (hSg : Sgv ≤ a + b' + S + 1 + lg) (he : e₀ ≤ 160 * Sgv) :
    (N + 1) * r * e₀ + 0 * e₀ ≤ C * (N + 1) * r * (a + b' + S + 1 + lg + η * bd) + C * N * m * e' := by
  have h1 : 0 ≤ η * bd := mul_nonneg hη hbd
  have hX : e₀ ≤ C * (a + b' + S + 1 + lg + η * bd) := by
    have h3 : 0 ≤ a + b' + S + 1 + lg + η * bd := by linarith
    nlinarith
  have hNr : 0 ≤ (N + 1) * r := by positivity
  have h4 : (N + 1) * r * e₀ ≤ (N + 1) * r * (C * (a + b' + S + 1 + lg + η * bd)) :=
    mul_le_mul_of_nonneg_left hX hNr
  have h5 : 0 ≤ C * N * m * e' := by
    have : 0 ≤ C := by linarith
    positivity
  nlinarith

theorem arith_one {C N r m e z e' a b' S lg η bd Sgv R : ℝ} (hC : 320 ≤ C) (hN : 0 ≤ N) (hr : 0 ≤ r)
    (hm : 0 ≤ m) (he' : 0 ≤ e') (ha : 0 ≤ a) (hb' : 0 ≤ b') (hS : 0 ≤ S) (hlg : 0 ≤ lg) (hη : 0 ≤ η)
    (hbd : 0 ≤ bd) (hR : 1 ≤ R) (hSg : Sgv ≤ a + b' + S + 1 + lg)
    (he : e ≤ 18 * Sgv + 3 * R ^ 2 * (S + 1 + lg) + 1) (hz : z ≤ (R + 1) * N * m) :
    (N + 1) * r * e + z * e' ≤
      C * (N + 1) * r * (a + b' + R ^ 2 * (S + 1 + lg) + η * bd) + C * N * m * R ^ 2 * e' := by
  have hR2 : 1 ≤ R ^ 2 := by nlinarith
  have hU : 1 ≤ S + 1 + lg := by linarith
  have hRU : S + 1 + lg ≤ R ^ 2 * (S + 1 + lg) := by nlinarith
  have h1 : 0 ≤ η * bd := mul_nonneg hη hbd
  have hY1 : 1 ≤ a + b' + R ^ 2 * (S + 1 + lg) + η * bd := by nlinarith
  have hX : e ≤ C * (a + b' + R ^ 2 * (S + 1 + lg) + η * bd) := by
    have h2 : e ≤ 40 * (a + b' + R ^ 2 * (S + 1 + lg) + η * bd) := by nlinarith
    nlinarith
  have hNr : 0 ≤ (N + 1) * r := by positivity
  have h4 : (N + 1) * r * e ≤ (N + 1) * r * (C * (a + b' + R ^ 2 * (S + 1 + lg) + η * bd)) :=
    mul_le_mul_of_nonneg_left hX hNr
  have hNm : 0 ≤ N * m := mul_nonneg hN hm
  have h5 : z * e' ≤ C * N * m * R ^ 2 * e' := by
    have h6 : R + 1 ≤ C * R ^ 2 := by nlinarith
    have : z ≤ C * N * m * R ^ 2 := by
      calc z ≤ (R + 1) * (N * m) := by linarith
        _ ≤ (C * R ^ 2) * (N * m) := mul_le_mul_of_nonneg_right h6 hNm
        _ = C * N * m * R ^ 2 := by ring
    exact mul_le_mul_of_nonneg_right this he'
  nlinarith

theorem thmB_at (C : ℝ) (hC : C0 ≤ C) {CR CA CB CK : ℝ} (hU : AdmBoundsB D HW F Cm CR CA CB CK)
    (hJ : UsedJ D HW F)
    (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL) (hK : CaseA K LL)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))] [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)] :
    TruncatedSeriesCountingBounds.ThmB ((D.loc l).PD K) ((HW l).W K 1 LL hG) C := by
  have hdvr : IsDiscreteValuationRing ↥(OL LL) := Formalism.BasicNotions.Examples₂.LB.OL_dvr LL
  intro hp T₁ T₂ f b w S η m up size Mi hi hS hw hη hS20 hnt
  dsimp only
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hB : HypB ((D.loc l).PD K) ((HW l).W K 1 LL hG) T₁ T₂ f b w S η m up size Mi hi :=
    ⟨hp, hS, hw, hη, hS20, hnt⟩
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hp0 : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ≠ 0 := by
    rw [hpl]
    intro h0
    have h1 := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h0
    simp only [ZeroMemClass.coe_zero] at h1
    exact (Nat.cast_ne_zero.2 (show l ≠ 0 from (Fact.out : l.Prime).ne_zero)) h1
  have hgen := hU.a10 l K LL hS.1.1 T₂ hS.2.1.2.1
  have hlift : f.LiftF ((D.loc l).PD K) (TruncatedSeriesCountingBounds.eLift ((HW l).W K 1 LL hG) T₁ Mi hi) :=
    hU.a2.2.2.2.2.2.2.2.1 l K 1 LL hG hS.1 T₁ T₂ f Mi hi hS.2.1 hS.2.2.2.2.2.2
  have hC0 : (320 : ℝ) ≤ C := hC
  rw [hpl]
  have hlg0 : 0 ≤ Real.logb (l : ℝ) (2 * (TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) := logb_two_mul_nonneg l _ hl2
  have hSg := sg_le_alt l b w S η size 0 hl2 le_rfl
  rw [mul_zero, add_zero] at hSg
  have ha0 : 0 ≤ (TruncatedSeriesCountingBounds.hB b w S η size : ℝ) / (l : ℝ) ^ 2 := by positivity
  have hb0 : 0 ≤ ((w : ℝ) + η) / (l : ℝ) := by positivity
  have hbd0 : 0 ≤ (if TruncatedSeriesCountingBounds.Band l b S η size
      (Real.logb (l : ℝ) (2 * (TruncatedSeriesCountingBounds.hB b w S η size : ℝ))) C then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  have hbdI : bandI l b w S η size C = (if TruncatedSeriesCountingBounds.Band l b S η size
      (Real.logb (l : ℝ) (2 * (TruncatedSeriesCountingBounds.hB b w S η size : ℝ))) C then (1 : ℝ) else 0) := rfl
  refine ⟨fun hAlt => ?_, fun R hR hup hrun => ?_⟩
  ·
    have hAlt' : Alt b η up size := hAlt
    by_cases hbig : (∃ i, TruncatedSeriesCountingBounds.Thick b η size i) ∧ (b : ℝ) / 4 < 40 * Sg l b w S η size
    · obtain ⟨e₀, he₀, hL₀⟩ := exists_liftF_le_sg_of_thick D HW F Cm hU l K LL hG hK T₁ T₂ f b w S η m up size Mi hi hB
        hAlt' hbig.1 hbig.2
      have hc := colLeR_of_exponent ((D.loc l).PD K) hp0 f _ e₀ e₀ hgen ∅ (by simp)
        (fun c hc => Submodule.mem_sup_left (hL₀ c hc)) hL₀
      refine colLeR_mono hc ?_
      have := arith_big (N := (Module.finrank ℚ_[l] ↥(K0 K) : ℝ)) (m := (m : ℝ)) (e' := ((TruncatedSeriesCountingBounds.eLift ((HW l).W K 1 LL hG) T₁ Mi hi : ℕ) : ℝ))
        hC0 (Nat.cast_nonneg _) (Nat.cast_nonneg (Module.finrank ↥LL.1 T₂.V)) (Nat.cast_nonneg m)
        (Nat.cast_nonneg _) ha0 hb0 (Nat.cast_nonneg S) hlg0 (Nat.cast_nonneg η) hbd0 hSg he₀
      rw [Finset.card_empty, Nat.cast_zero]
      push_cast at this ⊢
      linarith
    · have hsm : (¬ ∃ i, TruncatedSeriesCountingBounds.Thick b η size i) ∨ 40 * Sg l b w S η size ≤ (b : ℝ) / 4 := by
        by_cases ht : ∃ i, TruncatedSeriesCountingBounds.Thick b η size i
        · right; exact not_lt.mp fun h' => hbig ⟨ht, h'⟩
        · left; exact ht
      obtain ⟨e, Z, he, hZc, hZ, hZe⟩ := sum_alt D HW F Cm hU hJ l K LL hG hK T₁ T₂ f b w S η m up
        size Mi hi hB hAlt' C (by linarith) hsm
      have hc := colLeR_of_exponent ((D.loc l).PD K) hp0 f _ e _ hgen Z hZ hZe hlift
      refine colLeR_mono hc ?_
      rw [hbdI] at he
      have hz : (Z.card : ℝ) ≤ 4 * (Module.finrank ℚ_[l] ↥(K0 K) : ℝ) * m := by exact_mod_cast hZc
      have := arith_alt hC0 (Nat.cast_nonneg _) (Nat.cast_nonneg (Module.finrank ↥LL.1 T₂.V))
        (Nat.cast_nonneg m) (Nat.cast_nonneg (TruncatedSeriesCountingBounds.eLift ((HW l).W K 1 LL hG) T₁ Mi hi)) ha0 hb0
        (Nat.cast_nonneg S) hlg0 (Nat.cast_nonneg η) hbd0 hSg he hz
      push_cast at this ⊢
      linarith
  ·
    have hOne : One b η R up size := ⟨hup, hrun⟩
    obtain ⟨e, Z, he, hZc, hZ, hZe⟩ := sum_one D HW F Cm hU hJ l K LL hG hK T₁ T₂ f b w S η m up size
      Mi hi hB R hR hOne
    have hc := colLeR_of_exponent ((D.loc l).PD K) hp0 f _ e _ hgen Z hZ hZe hlift
    refine colLeR_mono hc ?_
    have hz : (Z.card : ℝ) ≤ ((R : ℝ) + 1) * (Module.finrank ℚ_[l] ↥(K0 K) : ℝ) * m := by
      exact_mod_cast hZc
    have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
    have := arith_one hC0 (Nat.cast_nonneg _) (Nat.cast_nonneg (Module.finrank ↥LL.1 T₂.V))
      (Nat.cast_nonneg m) (Nat.cast_nonneg (TruncatedSeriesCountingBounds.eLift ((HW l).W K 1 LL hG) T₁ Mi hi)) ha0 hb0
      (Nat.cast_nonneg S) hlg0 (Nat.cast_nonneg η) hbd0 hR1 hSg he hz
    push_cast at this ⊢
    linarith

theorem frobenius_statement_of_inputs (C : ℝ) (hC : C0 ≤ C) {CR CA CB CK : ℝ}
    (p2 : Formalism.MainNotions.DeltaInvariantLattices.P2 D HW F) (p3 : Formalism.MainNotions.DeltaInvariantLattices.P3 D HW F Cm) (p4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm)
    (p5 : Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F) (p9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) (a2 : ArcLiftingSetup.adm2 D HW F CR CA CB CK) (a5 : ArcLiftingSetup.adm5 D HW F)
    (sP : ArcLiftingSetup.SaturationFrobeniusPullback D HW F) (kLev : ArcLiftingSetup.KillerLevL D.loc D.locA HW F)
    (kMod : ArcLiftingSetup.KillerModL D.loc D.locA HW F) (a9 : ArcLiftingSetup.adm9 D) (a10 : ArcLiftingSetup.adm10 D)
    (a11 : ArcLiftingSetup.adm11 D HW F) (a12 : ArcLiftingSetup.adm12 D HW F Cm) (a13 : ArcLiftingSetup.adm13 D HW F Cm)
    (a14 : ArcLiftingSetup.adm14 D HW F Cm) (a15 : ArcLiftingSetup.adm15 D) (a22 : Formalism.MainNotions.CrystallineLiftingBounds.adm22 D HW F)
    (a23 : Formalism.MainNotions.CrystallineLiftingBounds.adm23 D HW F) (c4 : Formalism.MainNotions.N.LetterConditionGlobal D HW F) :
    ArcLiftingSetup.aux₃ D HW F C := by
  intro l _ K LL hG hKur _ _ h11
  have hl : 11 ≤ l := (D.loc l).PD_p K ▸ h11
  exact thmB_at D HW F Cm C hC ⟨p2, p3, p4, p5, p9, a2, a5, sP, kLev, kMod, a9, a10, a11, a12, a13, a14, a15⟩ ⟨a22, a23, c4⟩ l K LL hG
    ⟨hKur, by omega, hG⟩ h11

theorem stmt_holds (a22 : Formalism.MainNotions.CrystallineLiftingBounds.adm22 D HW F) (a23 : Formalism.MainNotions.CrystallineLiftingBounds.adm23 D HW F)
    (c4 : Formalism.MainNotions.N.LetterConditionGlobal D HW F) (C : ℝ) (hC : C0 ≤ C)
    (CR CA CB CK Ckap : ℝ) : ArcLiftingSetup.Stmt D HW F Cm C CR CA CB CK Ckap := fun hA =>
  let h := admBoundsB_of_adm hA
  frobenius_statement_of_inputs D HW F Cm C hC h.p2 h.p3 h.p4 h.p5 h.p9 h.a2 h.a5 h.sP h.kLev h.kMod h.a9 h.a10 h.a11 h.a12 h.a13 h.a14 h.a15
    a22 a23 c4

theorem frobenius_statement_of_fontaine (C CR CA CB CK Ckap : ℝ) (hC : (320 : ℝ) ≤ C) (a22 : Formalism.MainNotions.CrystallineLiftingBounds.adm22 D HW F)
    (a23 : Formalism.MainNotions.CrystallineLiftingBounds.adm23 D HW F) (c4 : Formalism.MainNotions.N.LetterConditionGlobal D HW F) :
    ArcLiftingSetup.Stmt D HW F Cm C CR CA CB CK Ckap :=
  stmt_holds D HW F Cm a22 a23 c4 C hC CR CA CB CK Ckap

end Record

theorem stmtF_holds (Dm : Formalism.MainNotions.DFamP) (L : Formalism.MainNotions.ArcLiftingSetup.LayF Dm)
    (hJ : ∀ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 52) (x : ℝ) (i : (Dm ε h0 h1).Ix x),
      UsedJ ((Dm ε h0 h1).D x i) (L ε h0 h1 x i).1 (L ε h0 h1 x i).2.1) : ArcLiftingSetup.KudlaFamilyStatement Dm L := by
  rintro ⟨CR, CA, CB, CK, Ckap, h⟩
  refine ⟨C0, fun ε h0 h1 => ?_⟩
  obtain ⟨x0, hx⟩ := h ε h0 h1
  exact ⟨x0, fun C hC x hx0 i => stmt_holds _ _ _ _ (hJ ε h0 h1 x i).a22 (hJ ε h0 h1 x i).a23 (hJ ε h0 h1 x i).c4 C hC
    CR CA CB CK Ckap (hx x hx0 i)⟩

end Formalism.MainNotions.N.Ln17
