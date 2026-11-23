import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsDeco
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.RowAct

section Gen

variable {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)

theorem parLev_of_Q (q : (levEnv V β L).Q) :
    Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _) ∈ parLev D.sp.cm V.gram β L := q.2.1

def rTupQ : (levEnv V β L).Q →* G0 L.Pg L.r where
  toFun q := rTup β L (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _))
  map_one' := by
    simp only [OneMemClass.coe_one, map_one]
    exact rTup_one
  map_mul' x y := by
    simp only [Subgroup.coe_mul, map_mul]
    exact rTup_mul (parLev_of_Q V β L x) (parLev_of_Q V β L y)

theorem rTupQ_apply (q : (levEnv V β L).Q) :
    rTupQ V β L q = rTup β L (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _)) := rfl

theorem rTupQ_eq_one_iff (q : (levEnv V β L).Q) :
    rTupQ V β L q = 1 ↔ ((q : Bridge.Gf V)) ∈ (levEnv V β L).J := by
  constructor
  · intro h
    exact ⟨parLev_of_Q V β L q, Subgroup.mem_bot.2 h⟩
  · intro h
    exact Subgroup.mem_bot.1 h.2

end Gen

end GlobalTheory.Mem.R3.RowAct
