import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.RegXInst
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
import Formalism.LocalToGlobal.ProjectiveLattices.LocRingPf
import Formalism.LocalToGlobal.ProjectiveLattices.TieInst
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
import Formalism.LocalToGlobal.ProjectiveLattices.CurveSec
import Formalism.LocalToGlobal.ProjectiveLattices.LiftSec
import Formalism.LocalToGlobal.ProjectiveLattices.LiftModelHolds
import Formalism.LocalToGlobal.ProjectiveLattices.SecPtRed
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CurveModelExistsAllPrimesAllPoints
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CurveSectionStatementStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CurveSectionAlt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionRatiosIntegral
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.RealPtNZOfCurveHyp

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PrimeData

section General

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem ev_ne_zero_of_nonZeroComp (X : PJ D B P j) {ι : Type} (Ω : ι → Type) [∀ Z, Field (Ω Z)]
    [∀ Z, Algebra B.KO (Ω Z)] (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)
    (hinj : ∀ (w : WeightFamilies.Wt D j) (g : B.Cusp j w), (∀ Z, gF Z (X.inc w g) = 0) → g = 0)
    {u : WeightFamilies.Wt D j} {F : B.Cusp j u} (hF : X.NonZeroComp u F) (Z : ι) {w : WeightFamilies.Wt D j} (g : B.Cusp j w)
    (hg : gF Z (X.inc w g) ≠ 0) (hg' : ∀ Z', Z' ≠ Z → gF Z' (X.inc w g) = 0) : gF Z (X.inc u F) ≠ 0 := by
  intro h0
  obtain ⟨H, hH⟩ := X.inc_mul u w F g
  have hH0 : H = 0 := by
    refine hinj _ H fun Z' => ?_
    rw [← hH, map_mul]
    by_cases hZ : Z' = Z
    · subst hZ
      rw [h0, zero_mul]
    · rw [hg' Z' hZ, mul_zero]
  rw [hH0, map_zero] at hH
  have := hF w g hH
  rw [this, map_zero, map_zero] at hg
  exact hg rfl

theorem ne_zero_of_nval_eq {T T' : CDVR} {e : ℕ} {x : T.Fr} {x' : T'.Fr} (hx : x ≠ 0)
    (h : nval T.V e x = nval T'.V e x') : x' ≠ 0 := by
  rintro rfl
  rw [nval_zero, nval_of_ne hx] at h
  exact EReal.coe_ne_top _ h

variable {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E} {ka wL wF : WeightFamilies.Wt D j}

theorem finiteDimensional_of_model {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}
    {g0 : B.Cusp j wF} (C : CurveModel G la g0) :
    FiniteDimensional (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) := by
  have : FiniteDimensional (Kp (xplus X E hM) la G.N) (↥C.A' ⧸ C.JA) := C.fin
  exact LinearEquiv.finiteDimensional C.quotEquiv.toLinearEquiv

theorem isReduced_of_model {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}
    {g0 : B.Cusp j wF} (C : CurveModel G la g0) : IsReduced (OsK (xplus X E hM) la G.w) := by
  have : IsReduced (↥C.A' ⧸ C.JA) := C.red
  exact isReduced_of_injective C.quotEquiv.symm.toRingHom C.quotEquiv.symm.injective

theorem data_of_real (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (S : Scal B)
    (g0 : B.Cusp j wF) (hC : Nonempty (CurveModel G la g0)) (hspan : SpanW (xplus X E hM) G.w S)
    (hmin : GenericSectionMinimumIntegral G la) (h1 : ESecSt G la) (h2 : Formalism.L2.Pj.LocStructSt G la)
    (hR : ∀ ζ : PtsG G la, ∃ (y : E.Pt' la) (hw : FromW ζ y),
      hw.ev (emb (xplus X E hM) la G.N (X.inc wF g0)) ≠ 0 ∧
      (j < D.R.m → hw.ev (emb (xplus X E hM) la G.N (X.inc _ G.et)) ≠ 0))
    (Gc Prw : ℝ) (Tn : ℕ) :
    ∃ Q : LocalPointData G la, Q.InCurve ∧ Q.InTie S ∧ Q.InLiftC S Gc Prw Tn := by
  choose y hw hg0 het using hR
  have hcur := inCurveSec G la y (fun ζ => (hw ζ).toSecPt) g0 hC hg0
  refine ⟨secQ y (fun ζ => (hw ζ).toSecPt) g0, hcur, ?_, ?_⟩
  · exact inTieSec D B P j X E hM ka wL wF G la S y (fun ζ => (hw ζ).toSecPt) g0
      (fun ζ => depthAtSec_of S hspan hmin hcur.1 hcur.2.1 y (fun ζ => (hw ζ).toSecPt) ζ) (fun hj ζ => het ζ hj) hg0 hcur.2.2
  · exact inLiftSec G la S Gc Prw y (fun ζ => (hw ζ).toSecPt) g0 Tn
      (liftModelSt_of G la (locRing_of h1 h2) y hw g0 Tn hC hg0)

end General

section Inst

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)

include hT in

theorem nzAt_of_nonZeroComp (hV : GenValInjSt h j hG) (hC : CompSplitSt h j hG) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (hB : BigAt h j hj hG G) {u : WeightFamilies.Wt D j}
    (F : (recB h.toLawsCore).Cusp j u) (hF : (recPlus h j hj).NonZeroComp u F) : NZAt hG (F : T.R j) := by
  intro Z
  obtain ⟨k, hk, -⟩ := hB.2 Z
  obtain ⟨g, e1, e2⟩ := hC Z wL (G.w k)
  have := ev_ne_zero_of_nonZeroComp (recPlus h j hj) (fun Z => Om Z) (fun Z => formsEvR j hG hT Z)
    (fun w g hg => hV w g fun Z => (formsEvR_inc h j hj hG hT Z w g).symm.trans (hg Z)) hF Z g
    (fun h0 => hk (e1.symm.trans ((formsEvR_inc h j hj hG hT Z wL g).symm.trans h0)))
    (fun Z' hZ' => (formsEvR_inc h j hj hG hT Z' wL g).trans (e2 Z' hZ'))
  exact fun h0 => this ((formsEvR_inc h j hj hG hT Z u F).trans h0)

theorem fromW_ne_zero {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO))
    (hU : IsUnif (OsK (recPlus h j hj) la G.w) (unifO (recPlus h j hj) la G.N)) [∀ ζ : PtsG G la, IsDVRAt ζ]
    (hR : RealPtNZSt h j hj hG G la hU) (ζ : PtsG G la) :
    ∃ (y : (extAll h j hj).Pt' la) (hw : FromW (E := extAll h j hj) (hM := intAtExt_extAll h j hj) ζ y),
      ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w), NZAt hG (F : T.R j) →
        hw.ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F)) ≠ 0 := by
  obtain ⟨y, Tc, ι, hl, hunr, ev, hu, hv, hdeg, hnz⟩ := hR ζ
  obtain ⟨hw⟩ := @fromW_of D (recB h.toLawsCore) T.G.P j (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj)
    ka wL wF G la ζ (‹∀ ζ : PtsG G la, IsDVRAt ζ› ζ) y hU Tc ι hl hunr ev hu hv hdeg
  exact ⟨y, hw, fun w F hF => ne_zero_of_nval_eq (hnz w F hF) ((hv w F).symm.trans (hw.hv w F))⟩

end Inst

theorem exists_primeData : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → (∀ (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF), BigAt h j hj hG G → BIRSt h j hj hG G) → 0 < wL.n → (j < D.R.m → (recPlus h j hj).NonZeroComp _ G.et) → ∀ (Gc Prw : ℝ) (Tn : ℕ), ∃ Qf : ∀ la, LocalPointData G la, (∀ la, (Qf la).InCurve) ∧ (∀ la, (Qf la).InTie S) ∧ (∀ la, (Qf la).InLiftC S Gc Prw Tn) := by
  intro D T h j hj hG hT ka wL wF G S g0 hH hV hC hB hB' hn het Gc Prw Tn
  have key : ∀ la, ∃ Q : LocalPointData G la, Q.InCurve ∧ Q.InTie S ∧ Q.InLiftC S Gc Prw Tn := by
    intro la
    have hM := GlobalTheory.CurveRecord.curveInst D T h j hj hG hT hV hC hB' hG ka wL wF G la S g0 hH.1 hH.2.1 hH.2.2.1 hH.2.2.2
    obtain ⟨C⟩ := id hM
    have hfd := finiteDimensional_of_model (E := extAll h j hj) (hM := intAtExt_extAll h j hj) C
    have hred := isReduced_of_model (E := extAll h j hj) (hM := intAtExt_extAll h j hj) C
    have hU : IsUnif (OsK (recPlus h j hj) la G.w) (unifO (recPlus h j hj) la G.N) := isUnif_of_ring hfd
    have hD : ∀ ζ : PtsG G la, IsDVRAt ζ := isDVRAt_of_ring hfd hred
    have hR := GlobalTheory.realPtNZ_of_curveHyp D T h j hj hG hT ka wL wF G S g0 la hH hV hC hB hn hU
    refine data_of_real (E := extAll h j hj) (hM := intAtExt_extAll h j hj) G la S g0 hM hH.1
      (GlobalTheory.Reg.section_ratios_integral D T h j hj hG hT ka wL wF G S g0 la hH hV hC hB hM)
      (GlobalTheory.T.curve_section_statement D T h j hj hG hT ka wL wF G S g0 la hH hV hC hB)
      (GlobalTheory.T.locStructSt_of_curveHyp D T h j hj hG hT ka wL wF G S g0 la hH hV hC hB) (fun ζ => ?_) Gc Prw Tn
    obtain ⟨y, hw, hnz⟩ := fromW_ne_zero h j hj hG G la hU hR ζ
    exact ⟨y, hw, hnz wF g0 (nzAt_of_nonZeroComp h j hj hG hT hV hC G hH.2.1 g0 hH.2.2.2),
      fun hlt => hnz _ G.et (nzAt_of_nonZeroComp h j hj hG hT hV hC G hH.2.1 G.et (het hlt))⟩
  choose Qf h1 h2 h3 using key
  exact ⟨Qf, h1, h2, h3⟩

end GlobalTheory.PrimeData
