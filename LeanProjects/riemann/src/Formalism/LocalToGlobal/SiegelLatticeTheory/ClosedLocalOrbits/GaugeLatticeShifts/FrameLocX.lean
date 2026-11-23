import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFrameWZeroExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem frameLoc_X (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    FrameLoc (X.B.I.ε v) D.R.k (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u'))
      (Tw u) (Tw u') where
  dim := (Formalism.L2.SG.Pf.card_frame X).symm
  k_pos := by have := D.R.m_add_three_le_k; omega
  sig := Formalism.L2.SG.PoincareInHH.Cut.card_eps_false X v
  e_li := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h := congrArg (hJ (X.B.I.ε v) (rv X.B.I v (X.fR j))) hg
    rw [hJ_fsum_r] at h
    have hfe : ∀ i, hJ (X.B.I.ε v) (rv X.B.I v (X.fR j)) (rv X.B.I v (X.eR i)) = if i = j then 1 else 0 :=
      fun i => (hJ_X X v _ _).trans (by rw [Formalism.L2.SG.PoincareInHH.Cut.hT_f_e X]; split_ifs <;> simp)
    simp only [hfe, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    rw [h]
    unfold hJ
    simp
  ee := fun a b => (hJ_X X v _ _).trans (by rw [X.ee]; simp)
  ez := fun a => (hJ_X X v _ _).trans (by rw [(X.zu_orth u a).1]; simp)
  ez' := fun a => (hJ_X X v _ _).trans (by rw [(X.zu_orth u' a).1]; simp)
  zz := (hJ_X X v _ _).trans (by rw [X.zu_norm u]; simp [Tw])
  zz' := (hJ_X X v _ _).trans (by rw [X.zu_norm u']; simp [Tw])
  T_pos := Tw_pos u
  T'_pos := Tw_pos u'

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
