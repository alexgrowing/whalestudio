import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCartanInvOneOfOnb
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardLiftAdjointEqUpwardThetaIntegralStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffSpaceLevelFixesFockVectors
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockVacOmFin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealLow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivAtOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCoeffVanishesOffLevelBadPlacesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIPEqStarL2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndexSumOfRank
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnderEqOfConj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelSubgroupRestrictedProductOfLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormIntegralStarMulSqLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisVec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveOfInnerEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InnerNeSpherical
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsFinIdem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RawLiftOntoOfUpInj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatSpanOfLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointInjectiveSurjectiveAndPositiveScalar

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RawLift

theorem innerPos_of_innerNe {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (h : InnerNe R i t S) : InnerPos R i t S := by
  unfold InnerPos
  intro th hth c
  have h' := h th hth c
  obtain ⟨l, hl, hx⟩ := h'
  have key := (GlobalTheory.adjoint_injective_surjective_and_positive_scalar _ _ th).2 (part R i S c) l hl hx
  obtain ⟨l', hl', hx', -⟩ := key
  exact ⟨l', hl', hx'⟩

theorem rawLift_main : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → RallisConv D →
    ThOnto R ∧ ∀ i t, UpInj R i t ∧ InnerPos R i t ∅ ∧ PartsSpan R i ∅ := by
  intro hC D G _ _ Pl0 T A Ks _ _ _ R F hL hF hR
  have lp : ∀ i, LevProd R i := GlobalTheory.LevelProduct.levProd_of_laws D G Pl0 T A Ks R F hL hF
  have tr : ∀ i, TransLaws R i := GlobalTheory.RawLiftTrans.transLaws hC D G Pl0 T A Ks R F hL hF
  have lf : ∀ i t, LevFix R i t := GlobalTheory.RawLift.LevelFix.levFix D G Pl0 T A Ks R F hL hF
  have vn : ∀ i t, VecNe R i t := vecNe D G Pl0 T A Ks R F hL hF
  have fs : ∀ i t, FinSum R i t := fun i t =>
    GlobalTheory.RawLift.finSum_of_rallis hC D G Pl0 T A Ks R F hL hF hR i t (GlobalTheory.T.downwardLift_adjoint_eq_upwardThetaIntegral hC D G Pl0 T A Ks R F hL hF i t) (lf i t)
      (GlobalTheory.RawLift.FactorInf.factInf D G Pl0 T A Ks R F hL hF i t) (GlobalTheory.RawLift.RealLowPf.realLow D G Pl0 T A Ks R F hL hF i t) (vn i t) (lp i) (tr i)
  have fm : ∀ i t, FinMult R i t := GlobalTheory.RawLift.LocalFactor.finMult D G Pl0 T A Ks R F hL hF
  have bs : ∀ i t, BadSupp R i t := GlobalTheory.T.localCoeff_vanishes_offLevel_badPlaces D G Pl0 T A Ks R F hL hF
  have ls : ∀ i t, LocSmall R i t := fun i t =>
    GlobalTheory.RawLift.Small.locSmall D G Pl0 T A Ks R F hL hF i t (bs i t) (GlobalTheory.RawLift.GoodModulus.goodMod D G Pl0 T A Ks R F hL hF i t)
      (GlobalTheory.IndexCount.indexSum_holds D G Pl0 T A Ks R F hL hF i)
  have up : ∀ i t, UpInj R i t := fun i t =>
    GlobalTheory.UpInj.upInj_holds D G Pl0 T A Ks R F hL hF i t (fs i t) (fm i t) (lf i t) (vn i t) (ls i t) (lp i) (tr i)
  refine ⟨GlobalTheory.rawLift_onto_of_upInj D G Pl0 T A Ks R F hL hF (GlobalTheory.RatSpanProof.ratSpan_of_laws D G Pl0 T A Ks R F hL hF) (fun i => up i A.μ0),
    fun i t => ⟨up i t, ?_, GlobalTheory.PartsSpanProof.partsSpan hC D G Pl0 T A Ks R F hL hF i ∅⟩⟩
  exact innerPos_of_innerNe R i t ∅
    (GlobalTheory.RawLift.innerNe_spherical D G Pl0 T A Ks R F hL hF i t (fs i t) (fm i t) (lf i t) (vn i t) (ls i t) (bs i t) (lp i) (tr i))

end GlobalTheory.RawLift
