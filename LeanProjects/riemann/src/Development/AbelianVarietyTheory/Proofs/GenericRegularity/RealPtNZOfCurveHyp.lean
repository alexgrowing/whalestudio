import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.RegXInst
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
import Formalism.LocalToGlobal.ProjectiveLattices.TieInst
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtMain
import Formalism.LocalToGlobal.ProjectiveLattices.PtOfSPf
import Formalism.LocalToGlobal.ProjectiveLattices.CompFin
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIntegralFramesModelInvertiblePushforward
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NatCastMemMaximalIdealOfOverLa
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliExistenceAndModuliScheme
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CountQAtStGenericSectionPrimes

set_option synthInstance.maxHeartbeats 400000

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

set_option maxHeartbeats 4000000 in

theorem realPtNZ_of_curveHyp : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF) (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → 0 < wL.n → ∀ (hU : IsUnif (OsK (recPlus h j hj) la G.w) (unifO (recPlus h j hj) la G.N)) [∀ ζ : PtsG G la, IsDVRAt ζ], RealPtNZSt h j hj hG G la hU := by
  intro D T h j hj hG hT ka wL wF G S g0 la hH hV _ hB hwL hU _
  obtain ⟨-, hbc, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hany, htw, -, -⟩ := GlobalTheory.lawsFieldsSeparately
  obtain ⟨hgood, -, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  obtain ⟨hpq, hr, -⟩ := hnum j hj
  have := CompFin.finite_comp (T.Q.Xo j) T.Q.c
  obtain ⟨-, -, -, hWt, -⟩ := GlobalTheory.Frames.algebraic_laws hbc _ _ _ _ (T.Q.Xo j) T.Q.c
  exact realPt_of h j hj hG G la hU hwL
    (ptOfS_of h j hj hG hany htw hT hV G hB la (GlobalTheory.SecCount.countQAtSt D T h j hj hG hT ka wL wF G S g0 la hH)) hT
    (GlobalTheory.intFrames_of_laws hbc htw _ _ _ _ (T.Q.Xo j) T.Q.c) hWt
    (GlobalTheory.Frames.modelAtSt_of_good GlobalTheory.Moduli.jointExistence_and_moduliScheme.1 GlobalTheory.Moduli.jointExistence_and_moduliScheme.2 _ _ _ _ (T.Q.Xo j) T.Q.c (hpq ▸ hr) hgood la)

end GlobalTheory
