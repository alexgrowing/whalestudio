import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FiniteReducedSection
import Formalism.LocalToGlobal.ProjectiveLattices.CurveInj
import Formalism.LocalToGlobal.ProjectiveLattices.CurveUnit
import Formalism.LocalToGlobal.ProjectiveLattices.CompFin
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FinrankHostDivTwo
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CurveRecord

theorem ev_ne_zero_of_nonZeroComp {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
    {ι : Type} (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)] (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)
    (hinj : ∀ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), (∀ Z, gF Z (X.inc u F) = 0) → F = 0)
    {wF wL : WeightFamilies.Wt D j} (g0 : B.Cusp j wF) (hg : X.NonZeroComp wF g0) (Z : ι) (g : B.Cusp j wL)
    (h1 : gF Z (X.inc wL g) ≠ 0) (h2 : ∀ Z', Z' ≠ Z → gF Z' (X.inc wL g) = 0) : gF Z (X.inc wF g0) ≠ 0 := by
  intro h0
  obtain ⟨H, hH⟩ := X.inc_mul wF wL g0 g
  have hz : H = 0 := by
    refine hinj _ H fun Z' => ?_
    rw [← hH, map_mul]
    by_cases e : Z' = Z
    · subst e
      rw [h0, zero_mul]
    · rw [h2 Z' e, mul_zero]
  have hg0 : g = 0 := hg wL g (by rw [hH, hz, map_zero])
  exact h1 (by rw [hg0, map_zero, map_zero])

section Inst

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)

include hT in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem evC_ne_zero (hV : GenValInjSt h j hG) (hC : CompSplitSt h j hG) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (hB : BigAt h j hj hG G) (g0 : (recB h.toLawsCore).Cusp j wF)
    (hg : (recPlus h j hj).NonZeroComp wF g0) (Z : Comp (T.Q.Xo j) T.Q.c) :
    evC hG Z ((g0 : (recB h.toLawsCore).Cusp j wF) : T.R j) ≠ 0 := by
  obtain ⟨k, hk, -⟩ := hB.2 Z
  obtain ⟨g, h1, h2⟩ := split_of h j hj hG hT hC G Z k
  have := ev_ne_zero_of_nonZeroComp (recPlus h j hj) (fun Z : Comp (T.Q.Xo j) T.Q.c => Om Z)
    (fun Z => formsEvR j hG hT Z)
    (fun u F hF => hV u F fun Z => (formsEvR_inc h j hj hG hT Z u F).symm.trans (hF Z)) g0 hg Z g
    (fun h0 => hk ((formsEvR_inc h j hj hG hT Z wL (G.w k)).symm.trans (h1.symm.trans h0))) h2
  exact fun h0 => this ((formsEvR_inc h j hj hG hT Z wF g0).trans h0)

end Inst

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem curveInst : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG), GenValInjSt h j hG → CompSplitSt h j hG → (∀ (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF), BigAt h j hj hG G → BIRSt h j hj hG G) → CurveInstSt h j hj := by
  intro D T h j hj hG hT hV hC hB
  haveI : Finite (Comp (T.Q.Xo j) T.Q.c) := CompFin.finite_comp _ _
  letI : Fintype (Comp (T.Q.Xo j) T.Q.c) := Fintype.ofFinite _
  obtain ⟨hfg, htr⟩ := GlobalTheory.FlagDim.fnFG_fnTrdeg_record D T.Q h.pins.2.2.2 j hj
  have hQ := countQAtSt_holds h j hj hG hT
  have hinj : ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ f : ↥(Frac0 (recPlus h j hj) la G.w), (∀ Z, phiI h j hj hG hT la G Z f = 0) → f = 0 :=
    fun ka wL wF G S g0 la _ f hf => curveInj h j hj hG hT hV G la f hf
  have hone := hone_of h j hj hG hT hC
  have hloc : ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ Z (r : RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w),
        ∃ a p : ↥(Frac0 (recPlus h j hj) la G.w),
          (∀ Q : Ideal ↥(Frac0 (recPlus h j hj) la G.w), Q.IsPrime → Jid (recPlus h j hj) la G.w ≤ Q →
            RingHom.ker (phiI h j hj hG hT la G Z) ≤ Q → p ∉ Q) ∧
          phiI h j hj hG hT la G Z p * r = phiI h j hj hG hT la G Z a := by
    intro ka wL wF G S g0 la hH Z r
    exact CurveLoc.loc_of_bir (recPlus h j hj) la G.N G.w (formsEvR j hG hT Z)
      (birAt_of h j hj hG hT G (hB ka wL wF G hH.2.1) Z) (hQ ka wL wF G S g0 la hH Z) r
  have hS1 := finite_reduced_section h j hj hG hT hfg htr
  refine curveInst_of h j hj hG hT hinj hone hloc hS1 ?_ ?_
  · intro ka wL wF G S g0 la hH e w' θ hw hθ
    have h1 := LocalUnitReduction.finRed (Kp (recPlus h j hj) la G.N) ↥(Frac0 (recPlus h j hj) la G.w)
      (Jid (recPlus h j hj) la G.w) (Comp (T.Q.Xo j) T.Q.c)
      (fun Z => RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w)
      (fun Z => phiI h j hj hG hT la G Z) (hinj _ _ _ G S g0 la hH) (hone _ _ _ G S g0 la hH)
      (hloc _ _ _ G S g0 la hH) (hS1 _ _ _ G S g0 la hH)
    exact unit_ideal_cusp_form_record h j hj hG hT G la g0 θ hw (hinj _ _ _ G S g0 la hH) (hone _ _ _ G S g0 la hH)
      (hloc _ _ _ G S g0 la hH) h1.1 (evC_ne_zero h j hj hG hT hV hC G hH.2.1 g0 hH.2.2.2) hθ
  · intro ka wL wF G S g0 la hH
    exact nonzero_divisor_cusp_form_record h j hj hG hT G la g0 (hinj _ _ _ G S g0 la hH)
      (evC_ne_zero h j hj hG hT hV hC G hH.2.1 g0 hH.2.2.2)

end GlobalTheory.CurveRecord
