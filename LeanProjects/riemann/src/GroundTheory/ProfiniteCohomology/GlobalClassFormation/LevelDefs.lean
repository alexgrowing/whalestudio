import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open GroundTheory.Global NumberField

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

noncomputable abbrev ideleClassRep : Rep ℤ Gal(L/K) :=
  Rep.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)

variable {K L}

omit [NumberField K] in

theorem ideleClassRep_ρ_apply (σ : Gal(L/K)) (x : Additive (IdeleClassGroup L)) :
    (ideleClassRep K L).ρ σ x = Additive.ofMul (σ • Additive.toMul x) :=
  rfl

end GroundTheory.ProfCoh
