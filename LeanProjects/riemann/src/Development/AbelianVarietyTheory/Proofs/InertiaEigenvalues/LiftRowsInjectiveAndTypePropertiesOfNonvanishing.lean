import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InnerPosOfInnerNe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftEigenformIsEigenform
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftGenerationFinitePlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftGenerationAtRealPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftPreservesGood
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodTypesExcludeLevelCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasStringOfLift
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsParamDefinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdjointComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeNZOfNonVanGen
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableContAut
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeOfMemPartW
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.DownLift

theorem liftRows_injective_and_typeProperties_of_nonvanishing : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → GlobalTheory.RawLift.RallisConv D → (∀ i t, NonVan R i t) → GlobalTheory.LiftRows.LiftInj R ∧ ∀ i t, TypeNZ R i t ∧ GoodMem R i t ∧ DownEig R i t ∧ UnrCorr R i t (fun _ => True) ∧ Saturated R i t := by
  intro hDec hHowe D G _ _ Pl0 T A Ks _ _ _ R F hG hFull hRallis hNV
  have hLaws : GlobalTheory.RawLift.Laws R F :=
    ⟨hG.core.lev, hG.core.grp, hG.core.fam, hG.core.models, hG.core.thP⟩
  have hTop5 := GlobalTheory.RawLift.rawLift_main hDec D G Pl0 T A Ks R F hLaws hFull hRallis
  have hEig : ∀ i t, DownEig R i t := GlobalTheory.DownEigen.downEig hHowe D G Pl0 T A Ks R F hG hFull
  have hGF : ∀ i t, GenFin R i t := GlobalTheory.DownLift.GenFinite.genFin hHowe D G Pl0 T A Ks R F hG hFull
  have hGI : ∀ i t, GenInf R i t := GlobalTheory.GenReal.genInf D G Pl0 T A Ks R F hG hFull
  have hGM : ∀ i t, GoodMem R i t := GlobalTheory.GoodLift.goodMem_of_given D G Pl0 T A Ks R F hG hFull
  have hNC : ∀ i t, GoodNoChi R i t := GlobalTheory.GoodTypeNoChi.goodNoChi D G Pl0 T A Ks R F hG hFull
  have hPar : ∀ i t, ParamsEx R i t := GlobalTheory.DownLift.Params.paramsEx hDec D G Pl0 T A Ks R F hG hFull
  have hIn : ∀ i t, UnrCorr R i t (fun w => Formalism.IndefR.Lev.IsConjPl w w) := GlobalTheory.DownInert.unrCorr_inert hHowe D G Pl0 T A Ks R F hG hFull
  have hSp : ∀ i t, UnrCorr R i t (fun w => ¬ Formalism.IndefR.Lev.IsConjPl w w) := GlobalTheory.SplitCorr.unrCorr_split D G Pl0 T A Ks R F hG hFull
  have hTNZ : ∀ i t, TypeNZ R i t := fun i t =>
    GlobalTheory.DownLift.typeNZ_of_nonVan_gen D G Pl0 T A Ks R F hG hFull i t (hNV i t) (hGI i t) (hGF i t) (hNC i t) (hGM i t)
  have hU : ∀ i t, UnrCorr R i t (fun _ => True) := by
    intro i t h hh s c y hy h1 h2 B B' hB hB' w hw _
    by_cases hc : Formalism.IndefR.Lev.IsConjPl w w
    · exact hIn i t h hh s c y hy h1 h2 B B' hB hB' w hw hc
    · exact hSp i t h hh s c y hy h1 h2 B B' hB hB' w hw hc
  refine ⟨GlobalTheory.LiftInjProof.liftInj_of_typeNZ D G Pl0 T A Ks R F hG hFull
      (fun i => ⟨hTNZ i A.μ0, hEig i A.μ0, hSp i A.μ0, hIn i A.μ0, hPar i A.μ0⟩), fun i t => ?_⟩
  refine ⟨hTNZ i t, hGM i t, hEig i t, hU i t, ?_⟩
  exact GlobalTheory.DownLift.Sat.saturated hDec hHowe D G Pl0 T A Ks R F hG hFull i t (hTNZ i t) (hEig i t) (hGM i t)
    ((hTop5.2 i t).1) (hU i t) (hPar i t)

end GlobalTheory.DownLift
