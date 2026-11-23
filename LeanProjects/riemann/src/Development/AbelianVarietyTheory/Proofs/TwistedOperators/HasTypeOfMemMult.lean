import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem hasType_of_mem_mult : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank), ∀ T ∈ Mult θ M (levG V β L : Set (GA D V)) (levChi V β L), ∀ v, HasType V β L (T v) := by
  intro D V S θ M β L T hT v
  induction hT using Submodule.span_induction generalizing v with
  | mem x hx => exact fun κ hκ h => hx.lev v κ hκ h
  | zero => intro κ _ h; simp
  | add x y _ _ hx hy =>
    intro κ hκ h
    simp only [MultilinearMap.add_apply, Pi.add_apply]
    rw [hx v κ hκ h, hy v κ hκ h, mul_add]
  | smul a x _ hx =>
    intro κ hκ h
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    rw [hx v κ hκ h, mul_left_comm]

end GlobalTheory
