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
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CurveSectionStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LocStructStRecord
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionRatiosIntegral
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.RealPtNZOfCurveHyp
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FiniteDimensionalOfModel

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PrimeData

section General

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}
variable {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E} {ka wL wF : WeightFamilies.Wt D j}

theorem secQ_data_of_real (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (S : Scal B)
    (g0 : B.Cusp j wF) (hC : Nonempty (CurveModel G la g0)) (hspan : SpanW (xplus X E hM) G.w S)
    (hmin : GenericSectionMinimumIntegral G la) (h1 : ESecSt G la) (h2 : Formalism.L2.Pj.LocStructSt G la)
    (hR : ∀ ζ : PtsG G la, ∃ (y : E.Pt' la) (hw : FromW ζ y),
      hw.ev (emb (xplus X E hM) la G.N (X.inc wF g0)) ≠ 0 ∧
      (j < D.R.m → hw.ev (emb (xplus X E hM) la G.N (X.inc _ G.et)) ≠ 0))
    (Gc Prw : ℝ) (Tn : ℕ) :
    ∃ (y : PtsG G la → E.Pt' la) (hw : ∀ ζ, FromW ζ (y ζ)),
      (secQ y (fun ζ => (hw ζ).toSecPt) g0).InCurve ∧ (secQ y (fun ζ => (hw ζ).toSecPt) g0).InTie S ∧
      (secQ y (fun ζ => (hw ζ).toSecPt) g0).InLiftC S Gc Prw Tn := by
  choose y hw hg0 het using hR
  have hcur := inCurveSec G la y (fun ζ => (hw ζ).toSecPt) g0 hC hg0
  refine ⟨y, hw, hcur, ?_, ?_⟩
  · exact inTieSec D B P j X E hM ka wL wF G la S y (fun ζ => (hw ζ).toSecPt) g0
      (fun ζ => depthAtSec_of S hspan hmin hcur.1 hcur.2.1 y (fun ζ => (hw ζ).toSecPt) ζ) (fun hj ζ => het ζ hj) hg0 hcur.2.2
  · exact inLiftSec G la S Gc Prw y (fun ζ => (hw ζ).toSecPt) g0 Tn
      (liftModelSt_of G la (locRing_of h1 h2) y hw g0 Tn hC hg0)

end General

theorem exists_real_primeData : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → (∀ (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF), BigAt h j hj hG G → BIRSt h j hj hG G) → 0 < wL.n → (j < D.R.m → (recPlus h j hj).NonZeroComp _ G.et) → ∀ (Gc Prw : ℝ) (Tn : ℕ), ∃ (y : ∀ la, PtsG G la → (extAll h j hj).Pt' la) (hw : ∀ la ζ, FromW (E := extAll h j hj) (hM := intAtExt_extAll h j hj) ζ (y la ζ)), (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InCurve) ∧ (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InTie S) ∧ (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InLiftC S Gc Prw Tn) := by
  intro D T h j hj hG hT ka wL wF G S g0 hH hV hC hB hB' hn het Gc Prw Tn
  have key : ∀ la, ∃ (y : PtsG G la → (extAll h j hj).Pt' la)
      (hw : ∀ ζ, FromW (E := extAll h j hj) (hM := intAtExt_extAll h j hj) ζ (y ζ)),
      (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) y (fun ζ => (hw ζ).toSecPt) g0).InCurve ∧
      (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) y (fun ζ => (hw ζ).toSecPt) g0).InTie S ∧
      (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) y (fun ζ => (hw ζ).toSecPt) g0).InLiftC
        S Gc Prw Tn := by
    intro la
    have hM := GlobalTheory.CurveRecord.curveInst D T h j hj hG hT hV hC hB' hG ka wL wF G la S g0 hH.1 hH.2.1 hH.2.2.1 hH.2.2.2
    obtain ⟨C⟩ := id hM
    have hfd := finiteDimensional_of_model (E := extAll h j hj) (hM := intAtExt_extAll h j hj) C
    have hred := isReduced_of_model (E := extAll h j hj) (hM := intAtExt_extAll h j hj) C
    have hU : IsUnif (OsK (recPlus h j hj) la G.w) (unifO (recPlus h j hj) la G.N) := isUnif_of_ring hfd
    have hD : ∀ ζ : PtsG G la, IsDVRAt ζ := isDVRAt_of_ring hfd hred
    have hR := GlobalTheory.realPtNZ_of_curveHyp D T h j hj hG hT ka wL wF G S g0 la hH hV hC hB hn hU
    refine secQ_data_of_real (E := extAll h j hj) (hM := intAtExt_extAll h j hj) G la S g0 hM hH.1
      (GlobalTheory.Reg.section_ratios_integral D T h j hj hG hT ka wL wF G S g0 la hH hV hC hB hM)
      (GlobalTheory.eSec_of_curveHyp D T h j hj hG hT ka wL wF G S g0 la hH hV hC hB)
      (GlobalTheory.Reg.locStructSt_record D T h j hj hG hT ka wL wF G S g0 la hH hV hC hB) (fun ζ => ?_) Gc Prw Tn
    obtain ⟨y, hw, hnz⟩ := fromW_ne_zero h j hj hG G la hU hR ζ
    exact ⟨y, hw, hnz wF g0 (nzAt_of_nonZeroComp h j hj hG hT hV hC G hH.2.1 g0 hH.2.2.2),
      fun hlt => hnz _ G.et (nzAt_of_nonZeroComp h j hj hG hT hV hC G hH.2.1 G.et (het hlt))⟩
  choose y hw h1 h2 h3 using key
  exact ⟨y, hw, h1, h2, h3⟩

end GlobalTheory.PrimeData
