import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.PairingCommutesLiftOperators
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfMemBoth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodFormsLeRangeThetaAdjointBaseTupleStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KernelProjectionPreservesGoodFormsBaseLevelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftInjectiveGoodPartJointEigenspaceStatement
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

namespace GlobalTheory.LiftOntoRed

theorem onto_red : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → LiftInj R.toRealDat → UpInjW R.toRealDat → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → R.toRealDat.LUnif → ∀ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW → U2.OntoC A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hW := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hC hEx hLI hUI hH hPG hLU hW hTh j
  exact GlobalTheory.OntoLinAlg.ontoParts_of _ (fun i x => hTh.intw j _ i x)
    (U2.adjoint_closed_lift_operators hH (RealDat3.kFormL_of hC.base.models) (RealDat3.jIsoL_of hC.base.models) j)
    (GlobalTheory.T.good_forms_le_range_theta_adjoint_base_tuple R F hok hC hEx hUI hH hPG hLU j) (GlobalTheory.T.kernelProjection_preserves_good_forms_base_level R F hok hC hEx hH hPG j)
    (GlobalTheory.T.thetaLift_injective_goodPart_jointEigenspace R F hok hC hEx hLI hH hPG j)

end GlobalTheory.LiftOntoRed
