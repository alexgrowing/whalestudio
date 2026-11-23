import Formalism.LocalToGlobal.CharacterGerms.RowTieDesc
import Formalism.LocalToGlobal.CharacterGerms.RowTiePEmbIntSt

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

open Formalism.L2.Pj

theorem nvalEqSt_holds : NvalEqSt := by
  intro T C _ V ι hι x
  unfold nval eOf
  have hl : 0 ≤ vV T.V ((V.l : ℕ) : T.Fr) := by
    have h := vV_algebraMap_nonneg T ((V.l : ℕ) : T.V)
    rwa [map_natCast] at h
  by_cases hx : x = 0
  · subst hx
    rw [if_pos rfl, map_zero, AddValuation.map_zero]
    rfl
  · rw [if_neg hx, hι x hx]
    have he : ((vV T.V ((V.l : ℕ) : T.Fr)).toNat : ℝ) = (vV T.V ((V.l : ℕ) : T.Fr) : ℝ) := by
      first
        | exact_mod_cast Int.toNat_of_nonneg hl
        | rw [← Int.cast_natCast (R := ℝ), Int.toNat_of_nonneg hl]
    rw [he]
    rfl

end Formalism.L2.FormalSeriesBounds
