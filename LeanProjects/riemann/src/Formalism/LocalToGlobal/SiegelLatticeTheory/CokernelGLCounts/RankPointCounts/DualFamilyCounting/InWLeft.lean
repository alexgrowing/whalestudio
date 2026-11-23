import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibCut

noncomputable section

open NumberField Formalism.BasicNotions Matrix
open scoped BigOperators

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

theorem h_symm (x y : (VS D).V) : (VS D).hT y x = star ((VS D).hT x y) := ((VS D).herm.eq x y).symm

theorem h_fe (a b : Fin D.R.rS) : (VS D).hT (X.fY a) (X.eX b) = if a = b then 1 else 0 := by
  rw [h_symm, X.ef b a]
  by_cases h : b = a
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h), star_zero]

theorem inW_pW (y : (VS D).V) : InW X (pW X y) := by
  intro c
  unfold pW
  simp only [map_sub, map_sum, map_smul, smul_eq_mul, X.ee, X.ef, h_fe, X.ff, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, sub_zero]
  constructor
  · simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]
  · simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]

theorem decomp (y : (VS D).V) :
    y = ∑ c, (VS D).hT (X.fY c) y • X.eX c + ∑ c, (VS D).hT (X.eX c) y • X.fY c + pW X y := by
  unfold pW
  abel

theorem inW_left {w : (VS D).V} (hw : InW X w) (a : Fin D.R.rS) :
    (VS D).hT w (X.eX a) = 0 ∧ (VS D).hT w (X.fY a) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [h_symm, (hw a).1, star_zero]
  · rw [h_symm, (hw a).2, star_zero]

end Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex
