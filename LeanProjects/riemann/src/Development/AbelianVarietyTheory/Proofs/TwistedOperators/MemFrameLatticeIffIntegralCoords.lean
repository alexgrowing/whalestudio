import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisOSumSmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRepSuppSplit
import Formalism.FockGram.SymGramPosSemidef
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section
namespace GlobalTheory.SplitVacAlg

variable {D : D7}

def frameLat (V : HSp D) : Submodule (𝓞 D.host.E) V.V := Submodule.span (𝓞 D.host.E) (Set.range V.frame)

theorem frameLat_isLattice (V : HSp D) : Submodule.IsLattice D.host.E (frameLat V) where
  fg := Submodule.fg_span (Set.finite_range _)
  span_eq_top := by
    rw [frameLat, Submodule.span_span_of_tower]
    exact V.frame.span_eq

theorem frameLat_unimod (V : HSp D) (hV : V.gram = 1) : Formalism.HermitianLatticesTheory.IsUnimodular V.hT (frameLat V) := by
  have key := (Formalism.E.hermDual (𝓞 D.host.E) D.host.E V.V (Fin V.rank) V.hT V.frame
    (IsFractionRing.injective (𝓞 D.host.E) D.host.E)
    (fun s => ⟨⟨star (s : D.host.E), s.2.map (starRingEnd D.host.E).toIntAlgHom⟩, rfl⟩)).2
    (1 : Matrix (Fin V.rank) (Fin V.rank) (𝓞 D.host.E)) (fun i j => by
      have := congrFun (congrFun hV i) j
      simp only [HSpace.gram] at this
      rw [this]
      by_cases h : i = j
      · subst h; simp
      · simp [h]) (by simp)
  exact key.2.2 (by simp)

def stdLatSp (V : HSp D) (hV : V.gram = 1) : HSp D :=
  { V with L0 := frameLat V, standardTuple_isLattice := frameLat_isLattice V, baseLattice_isUnimodular := frameLat_unimod V hV }

example (V : HSp D) (hV : V.gram = 1) : GA D (stdLatSp V hV) = GA D V := rfl

theorem mem_frameLattice_iff_integral_coords (V : HSp D) (hV : V.gram = 1) (y : Fin V.rank → D.host.E) :
    y ∈ L0c D (stdLatSp V hV) ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = y i := by
  change ∑ i, y i • V.frame i ∈ frameLat V ↔ _
  rw [frameLat, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩ i
    refine ⟨c i, ?_⟩
    have h1 : ∑ i, ((c i : D.host.E)) • V.frame i = ∑ i, y i • V.frame i := by
      rw [← hc]
      exact Finset.sum_congr rfl fun i _ => (algebraMap_smul D.host.E (c i) (V.frame i))
    have := congrArg (fun z => V.frame.repr z i) h1
    simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    exact this
  · intro h
    choose c hc using h
    refine ⟨c, Finset.sum_congr rfl fun i _ => ?_⟩
    rw [← hc i]
    exact (algebraMap_smul D.host.E (c i) (V.frame i)).symm

end GlobalTheory.SplitVacAlg
