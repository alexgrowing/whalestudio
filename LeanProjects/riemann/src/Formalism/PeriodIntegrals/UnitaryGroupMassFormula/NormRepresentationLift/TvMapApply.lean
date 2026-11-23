import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub

noncomputable section

open scoped Classical

namespace PI.NRL

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

def tvMap (e v : S.V) (l : E) : S.V →ₗ[E] S.V :=
  LinearMap.id + (S.hT v).smulRight e - (S.hT e).smulRight v + l • (S.hT e).smulRight e

theorem tvMap_apply (e v : S.V) (l : E) (y : S.V) :
    tvMap e v l y = y + S.hT v y • e - S.hT e y • v + (l * S.hT e y) • e := by
  simp only [tvMap, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.smulRight_apply, LinearMap.smul_apply, smul_smul]

theorem tvMap_comp (e v : S.V) (l μ : E) (hee : S.hT e e = 0) (hev : S.hT e v = 0)
    (hve : S.hT v e = 0) (y : S.V) :
    tvMap e (-v) μ (tvMap e v l y) = y + (S.hT e y * (l + S.hT v v + μ)) • e := by
  rw [tvMap_apply, tvMap_apply]
  simp only [map_add, map_sub, map_smul, map_neg, LinearMap.neg_apply, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, hee, hev, hve, smul_eq_mul, mul_zero, add_zero,
    sub_zero, smul_zero]
  module

end PI.NRL
