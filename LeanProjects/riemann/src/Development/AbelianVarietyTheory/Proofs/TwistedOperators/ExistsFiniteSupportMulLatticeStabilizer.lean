import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TruncAway

open GlobalTheory.AdelicU

theorem exists_trunc_mul_inK : ∀ {D : D7} (V : HSp D) (L : GlobalTheory.FinPl.Lat V), L.FG → Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ →
  ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (b : GA D V), ∃ (b' : GA D V) (P : Finset (HeightOneSpectrum (𝓞 D.host.F))),
    (∀ v ∉ P, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v b' = 1) ∧ GlobalTheory.FinPl.InK V L (fun v => v ∉ S) (b'⁻¹ * b) := by
  intro D V L hfg hspan S b
  haveI : Submodule.IsLattice D.host.E L := ⟨hfg, hspan⟩
  have hfin := Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc D.sp.cm.sig V.gram L b)
  classical
  let P : Finset (HeightOneSpectrum (𝓞 D.host.F)) := S ∪ hfin.toFinset
  let b' : GA D V := ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram b) *
    embAt D.sp.cm.sig V.gram P (projAt D.sp.cm.sig V.gram P b)
  have hat := mem_atPts.1 (embAt_mem D.sp.cm.sig V.gram P (projAt D.sp.cm.sig V.gram P b))
  have hout : ∀ v ∉ P, proj D.sp.cm.sig V.gram v b' = 1 := fun v hv => by
    simp only [b', map_mul, proj_ofInf, one_mul]
    exact hat.2 v hv
  have hin : ∀ v ∈ P, proj D.sp.cm.sig V.gram v b' = proj D.sp.cm.sig V.gram v b := fun v hv => by
    simp only [b', map_mul, proj_ofInf, one_mul]
    exact proj_embAt D.sp.cm.sig V.gram P _ ⟨v, hv⟩
  have hinf : projInf D.sp.cm.sig V.gram b' = projInf D.sp.cm.sig V.gram b := by
    simp only [b', map_mul, projInf_ofInf, mem_finPts.1 hat.1, mul_one]
  refine ⟨b', P, hout, ?_, ?_⟩
  · rw [GlobalTheory.FinPl.KOpen.mem_grpAt_iff]
    refine ⟨mem_finPts.2 ?_, fun v hv => ?_⟩
    · rw [map_mul, map_inv, hinf, inv_mul_cancel]
    · have hvP : v ∈ P := Finset.mem_union_left _ (not_not.1 hv)
      rw [map_mul, map_inv, hin v hvP, inv_mul_cancel]
  · refine GlobalTheory.FinPl.KOpen.moves_of_levelOpen V L hfg _ (mem_levelOpen.2 fun v => ?_)
    by_cases hv : v ∈ P
    · rw [map_mul, map_inv, hin v hv, inv_mul_cancel]; exact one_mem _
    · rw [map_mul, map_inv, hout v hv, inv_one, one_mul]
      by_contra h
      exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 h))

end GlobalTheory.TruncAway

end
