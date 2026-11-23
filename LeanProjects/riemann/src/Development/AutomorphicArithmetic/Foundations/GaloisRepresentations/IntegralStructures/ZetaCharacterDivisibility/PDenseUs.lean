import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutomorphicLevelAwayNonsplit
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.denseUs_of :
    DenseUs := by
  classical
  intro E Ω _ _ _ _ _ _ l _ a d hd U hU X
  have hfin := GlobalTheory.CongL.UnitLim.finite_not_sph a U hU
  refine (GlobalTheory.CongL.UnitLim.dense_frob_usable_off E Ω l Fact.out d hd (X ∪ hfin.toFinset)).mono ?_
  rintro g ⟨w, hw, hus, hl, -, A, hA, hg⟩
  refine ⟨w, fun h => hw (Finset.mem_union_left _ h), hus, hl, ?_, A, hA, hg⟩
  by_contra hB
  exact hw (Finset.mem_union_right _ (hfin.mem_toFinset.2 ⟨hus.1, hB⟩))
