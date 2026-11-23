import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondLinkOfWeightRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNormalisedTupleDataOverCoefficientField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChange
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsEx
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.LevVal

theorem envV_chi_mem {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (h : R.Char F)
    (j : Fin D.R.m) (t : T0) (k : (GlobalTheory.TraceIncl.envV R j t).J) :
    ∃ a : D.what₂.LL, D.what₂.embLL a = (((GlobalTheory.TraceIncl.envV R j t).χ k : ℂˣ) : ℂ) := by
  obtain ⟨a, ha⟩ := hχ_of R j t
    (fun PP hP u => let ⟨a, ha⟩ := GlobalTheory.ConjForms.chi_mem R h.grp.chiW j PP hP u; ⟨a, ha.symm⟩)
    (fun PP hP u => let ⟨a, ha⟩ := GlobalTheory.PinsOverField.xiR_mem R h.lev h.fam t PP hP u; ⟨a, ha.symm⟩) k
  exact ⟨a, ha.symm⟩

theorem chi_val : AtTw fun Fm x hx i p w j => ∀ k, ∃ a : (Fm.D x i).what₂.LL,
  (Fm.D x i).what₂.embLL a = (((GlobalTheory.TraceIncl.envV (R2 p) j ((R2 p).mu ((Fm.D x i).plEq w))).χ k : ℂˣ) : ℂ) :=
  AtTw.of_forall fun _ _ _ _ p hr hm _ _ j k =>
    envV_chi_mem (R2 p) (F2 p) (GlobalTheory.BigOn.links2_of_rows _ _ _ _ _ _ _ _ _ _ p hr hm.1).1 j _ k

end GlobalTheory.BigOn.LevVal
