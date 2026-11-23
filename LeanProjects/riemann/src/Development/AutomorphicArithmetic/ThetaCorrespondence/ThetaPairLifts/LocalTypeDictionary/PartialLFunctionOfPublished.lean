import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialLFunctionOfPublished
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LiftInjNonVanTypeNZOfPrints
import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.SecOfDm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialLFunctionFromPrintResultsStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
namespace GlobalTheory.LiftOntoOfPublished
theorem ontoC_of_hypotheses_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilSiegelFormulaUnitary → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.HeckeLPartialContinuation → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → HostHyp D → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → D.host.ccK = ⊤ → FWT.QGuard R.toRealDat → GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R.toRealDat → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → R.toRealDat.LUnif → ∀ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW → U2.OntoC A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hW := by
  intro hDSC hHCM hCusp hHowe hWSF hDbl hUnr hBZ hHeckeL D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hEx hHost hPar hcc hQ
    hGT hOkH hPG hLU hW hHT
  have hGiv : Given R.toRealDat F.lv2 :=
    GlobalTheory.GivenOfTop.given_of_top R F hOk hC hEx hHost hPar hcc hQ hGT
  have hFull : R.toRealDat.FullP := hC.fullP
  have hLI : LiftInj R.toRealDat :=
    (_root_.GlobalTheory.T.liftInj_and_nonVan_typeNZ_of_given hCusp hDbl hUnr hHeckeL hHowe _ _ _ _ _ _ R.toRealDat F.lv2 hGiv hFull).1
  have hSE : GlobalTheory.Published.SiegelEisensteinContinuation :=
    _root_.ResidueKilled.sec_of_dm hDbl
  have hCore := GlobalTheory.CoreOfWeak.core_of_weak R F hC hEx
  have hA : AForm R.toRealDat R.SF :=
    GlobalTheory.T.thetaInnerProduct_eq_const_mul_LValue hDSC hHCM hCusp hWSF hSE hUnr hBZ R.toRealDat F.lv2 hGiv hcc R.SF hCore.2.1
  have hUp : UpInjW R.toRealDat :=
    GlobalTheory.Core.Rk.UpInjWProof.upInjW_of_aForm _ _ _ _ _ _ R.toRealDat F.lv2 hCore.1
      (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCusp R.toRealDat) hGiv.irr R.SF hCore.2.1 hA
  exact GlobalTheory.T.thetaLift_onto_of_injective_eigenspaces R F hOk hC hEx hLI hUp hOkH hPG hLU hW hHT
end GlobalTheory.LiftOntoOfPublished
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_L_function_of_hypotheses_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilSiegelFormulaUnitary → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.HeckeLPartialContinuation → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → HostHyp D → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → D.host.ccK = ⊤ → FWT.QGuard R.toRealDat → GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R.toRealDat → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → R.toRealDat.LUnif → ∀ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW → U2.OntoC A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hW := by
  first | exact @_root_.GlobalTheory.LiftOntoOfPublished.ontoC_of_hypotheses_alt | exact _root_.GlobalTheory.LiftOntoOfPublished.ontoC_of_hypotheses_alt | (intros; apply _root_.GlobalTheory.LiftOntoOfPublished.ontoC_of_hypotheses_alt <;> assumption)
end
