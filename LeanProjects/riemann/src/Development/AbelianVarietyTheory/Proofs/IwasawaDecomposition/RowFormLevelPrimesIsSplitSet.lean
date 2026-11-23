import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.IndefiniteReal.BridgeColPts
import Formalism.LocalToGlobal.Columns.InputsGenus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsAtAndSeedFacts
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Mem.R3.LiftBrg

theorem mem_sgL_iff (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hL : LevOf X I U L) (t : TupU I U) (PP : Pl X.toD7.host.E) :
    PP ∈ sgL X I U t ↔ PP ∈ L.Pg ∨ PP ∈ L.Q t := by
  rw [hL.Pg, hL.Q t, Col2.ColIn.Q, tup_ixOf I t]
  classical
  exact Finset.mem_union

theorem isSplitSet_sgL : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → LevOf X I U L →
    ∀ t : TupU I U, Formalism.L2.DIV.IsSplitSet (LiftBrg.sgL X I U t) := by
  intro X px I U L _ hL t PP h PP' h' hc
  have hc' : Formalism.IndefR.Lev.IsConjPl (D := X.toD7) PP PP' := fun c hm =>
    ⟨Formalism.DivisionValues.cO X.toD7.host.E c, (hc c (Formalism.DivisionValues.cO X.toD7.host.E c) rfl).1 hm, rfl⟩
  exact GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hL.is t ((mem_sgL_iff X I U L hL t PP).1 h)
    ((mem_sgL_iff X I U L hL t PP').1 h') hc'

end GlobalTheory.Mem.R3.LiftBrg
