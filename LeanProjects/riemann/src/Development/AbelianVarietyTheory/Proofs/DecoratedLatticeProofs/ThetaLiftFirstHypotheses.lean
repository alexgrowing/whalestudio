import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SchurOrthogonalitySquareIntegrable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.SharpRestriction.ElevenLe
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartW
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaAdjointScalarTheoremOfScalarFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaInnerProductEqConstMulLValueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftAdjointScalarFormulaInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperspecialFixesVacuaGoodInertPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarHypothesesOfTopRowsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteTypeCarriesOnePartStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
namespace GlobalTheory.ThmAFinal

theorem pThmA_short
    (hDS : GlobalTheory.Published.DiscreteSeriesCover) (hHCF : GlobalTheory.Published.HarishChandraFinite)
    (hHCM : GlobalTheory.Published.HarishChandraModules) (hCW : GlobalTheory.Published.CasselmanWallach)
    (hCusp : GlobalTheory.Published.CuspRapidDecay) (hHowe : GlobalTheory.Hk3.HoweUnram)
    (hWS : GlobalTheory.Published.WeilSiegelFormulaUnitary) (hHk : ∀ D' : Formalism.BasicNotions.D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D')
    (hSE : GlobalTheory.Published.SiegelEisensteinContinuation) (hUD : GlobalTheory.Published.UnramifiedDoublingGL)
    (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) :
    ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → HostHyp D → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → D.host.ccK = ⊤ → FWT.QGuard R.toRealDat → GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R.toRealDat → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → R.PThmA := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hCh hEx hHost hLed hcc hQ hGT hInert
  obtain ⟨hCore, hSF, hE, hW⟩ := GlobalTheory.T.core_clauses_of_weak_characterisation R F hCh hEx
  have hGiven := GlobalTheory.T.scalarHypotheses_of_topRows R F hOk hCh hEx hHost hLed hcc hQ hGT
  have hFix := GlobalTheory.T.hyperspecial_fixes_vacua_good_inert_place R F hCh hEx
  have hA := GlobalTheory.T.thetaInnerProduct_eq_const_mul_LValue hDS hHCM hCusp hWS hSE hUD hBZ R.toRealDat F.lv2 hGiven hcc R.SF hSF
  have hU := (GlobalTheory.T.thetaLift_adjoint_scalarFormula_injective hDS hHCF hHCM hCW hCusp hHowe hWS hHk hSE hUD R.toRealDat F.lv2 hGiven hcc hCh.allPl hFix R.SF hSF).2
  have hC := GlobalTheory.T.finiteType_carriesOnePart hHowe hCusp R F hOk hCh hEx hInert hU
  exact GlobalTheory.T.thetaAdjoint_scalar_theorem_of_scalar_formula R F hOk hCh hEx hA hC

end GlobalTheory.ThmAFinal
