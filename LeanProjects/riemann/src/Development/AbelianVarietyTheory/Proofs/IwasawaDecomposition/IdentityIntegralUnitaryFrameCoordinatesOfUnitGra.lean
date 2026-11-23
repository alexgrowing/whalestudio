import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000

namespace GlobalTheory.Mem.R3.LiftBrg

theorem castGL_mem_UA_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) {m n : ℕ} (h : m = n) (x : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    castGL h x ∈ Formalism.L2.DIV.UA hc (1 : Matrix (Fin n) (Fin n) E) ↔
      x ∈ Formalism.L2.DIV.UA hc (1 : Matrix (Fin m) (Fin m) E) := by
  subst h
  have : castGL (rfl : m = m) x = x := by
    ext i j
    rfl
  rw [this]

theorem frameOK_one_of_gram_eq_one (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (i : Fin X.toD7.R.m) (t : TupU I U) (hg : (Vc X.toD7 i).gram = 1) : LiftBrg.FrameOK X I U i t 1 1 := by
  refine ⟨⟨1, (map_one _).symm⟩, one_mem _, fun x => ?_, one_mem _, one_mem _, fun PP _ => ?_⟩
  · rw [hg, one_mul, inv_one, mul_one]
    exact (castGL_mem_UA_one X.toD7.sp.cm (rkEq X i) x).symm
  · rw [one_mul]; exact one_mem _

end GlobalTheory.Mem.R3.LiftBrg
