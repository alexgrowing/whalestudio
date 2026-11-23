import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.ActQ

variable (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (U : Set I.ι)
  (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U))

theorem mem_parLev_of_Q (i : Fin X.toD7.R.m) (t : TupU I U) (q : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) :
    Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _) ∈
      Formalism.L2.DIV.parLev X.toD7.sp.cm (Vc X.toD7 i).gram (L.βV i) (L.datVt i t) := q.2.1

def rV (i : Fin X.toD7.R.m) (t : TupU I U) (x : GL (Fin (Vc X.toD7 i).rank) (Formalism.IndefR.Lev.EAf X.toD7)) : G0 L.Pg X.toD7.R.r :=
  rTup (L.βV i) (L.datVt i t) x

theorem rV_one (i : Fin X.toD7.R.m) (t : TupU I U) : rV X I U L i t 1 = 1 := rTup_one

theorem rV_mul (i : Fin X.toD7.R.m) (t : TupU I U) {x y : GL (Fin (Vc X.toD7 i).rank) (Formalism.IndefR.Lev.EAf X.toD7)}
    (hx : x ∈ Formalism.L2.DIV.parLev X.toD7.sp.cm (Vc X.toD7 i).gram (L.βV i) (L.datVt i t))
    (hy : y ∈ Formalism.L2.DIV.parLev X.toD7.sp.cm (Vc X.toD7 i).gram (L.βV i) (L.datVt i t)) :
    rV X I U L i t (x * y) = rV X I U L i t x * rV X I U L i t y := rTup_mul hx hy

def redQ (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (i : Fin X.toD7.R.m) (t : TupU I U) :
    (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q →* Gc X.B px where
  toFun q := eG.symm (rV X I U L i t
    (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)))
  map_one' := by
    simp only [OneMemClass.coe_one, map_one]
    rw [rV_one, map_one]
  map_mul' a b := by
    simp only [Subgroup.coe_mul, map_mul]
    rw [rV_mul X I U L i t (mem_parLev_of_Q X I U L i t a) (mem_parLev_of_Q X I U L i t b), map_mul]

theorem redQ_apply (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (i : Fin X.toD7.R.m) (t : TupU I U)
    (q : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) :
    redQ X I U L eG i t q = eG.symm (rV X I U L i t
      (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _))) := rfl

theorem eG_redQ (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (i : Fin X.toD7.R.m) (t : TupU I U)
    (q : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) :
    eG (redQ X I U L eG i t q) = rV X I U L i t
      (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) := by
  rw [redQ_apply]
  exact eG.apply_symm_apply _

theorem redQ_eq_one_iff (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (i : Fin X.toD7.R.m) (t : TupU I U)
    (q : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) :
    redQ X I U L eG i t q = 1 ↔ (q : Bridge.Gf (Vc X.toD7 i)) ∈ (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J := by
  rw [redQ_apply, MulEquiv.map_eq_one_iff]
  constructor
  · intro h
    exact ⟨mem_parLev_of_Q X I U L i t q, Subgroup.mem_bot.2 h⟩
  · intro h
    exact Subgroup.mem_bot.1 h.2

def ptS (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X)) (g : Bridge.Gf (Vc X.toD7 i)) :
    Formalism.L2.Col.DecoSet X.B.fields.E X.B.R.nV ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) :=
  ptL X I U i t A k g

def redZ (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X))
    (κ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) :
    Formalism.L2.Col.GLG X.B.fields.E X.B.R.nV (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) :=
  fun w => Formalism.L2.DIV.redFn (1 : GL (Fin X.B.R.nV) (EA X)) w.1
    ((A * k)⁻¹ * castGL (rkEq X i).symm
      (Formalism.UG.bc (swapAE X.toD7) ((κ : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) * (A * k))

end GlobalTheory.Mem.R3.LiftBrg.ActQ
