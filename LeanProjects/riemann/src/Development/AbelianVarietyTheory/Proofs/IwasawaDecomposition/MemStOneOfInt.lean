import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuCharacterDetLevelEqLocalTameProduct
import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.SelfDualFramesExistOfDiagonal
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Mem.R3.LiftBrg.StdFrame

section
attribute [local instance] Formalism.BasicNotions.Host.cmStar
end

theorem castGL_rfl {R : Type} [CommRing R] {m : ℕ} (x : GL (Fin m) R) : castGL (rfl : m = m) x = x := by
  ext i j
  simp [castGL]

section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end

theorem isSplitSet_sgL (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (U : Set I.ι) (hI : I.Ok) (t : TupU I U) :
    Formalism.L2.DIV.IsSplitSet (sgL X I U t) := by
  have hX := (GlobalTheory.Mem.Col2.base_fields_primes_ok X.B px).1
  have hPr := (GlobalTheory.Mem.Col2.base_fields_primes_ok X.B px).2.1
  intro P1 h1 P2 h2 h12
  have := GlobalTheory.LevMuDet.conjP_notMem_rowSG t.1 hX hPr hI.sel_ok hI.g_mem h1
  apply this
  have e : Formalism.L2.Col.conjPrime₂ P1 = P2 := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    ext r
    rw [Formalism.L2.Col.mem_conjP]
    refine h12 _ r ?_
    show (r : X.toD7.host.E) = star (star (r : X.toD7.host.E))
    rw [star_star]
  subst e; exact h2

end GlobalTheory.Mem.R3.LiftBrg.StdFrame

namespace GlobalTheory.Mem.R3.LiftBrg

end GlobalTheory.Mem.R3.LiftBrg
