import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesSplitIdempotentSum
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridLocalTensorPlaces_splitIdempotent_sum : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ t : T,
    (∀ w ∈ locPl G t, IsSplitIdem D (atPl w 1) ∧ atPl w 1 + cA D (atPl w 1) =
      algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV (w.under (𝓞 D.host.F)) 1)) ∧
    ∀ ε, IsIdemSum ε (locPl G t) → ε = ∑ w ∈ locPl G t, atPl w 1 ∧ ∀ w ∈ locPl G t, ε * atPl w 1 = atPl w 1 := by
  first | exact @GlobalTheory.IdemAtPl.main | exact GlobalTheory.IdemAtPl.main | (intros; apply GlobalTheory.IdemAtPl.main <;> assumption)
