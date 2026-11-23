import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowLeSpan
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.CoeffEmbedding

theorem continuous_iotaOQ_of_data : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
    (N : NData R H what₂) (A : NAut N) (i : N.Loc), Continuous (iotaOQ N A i) :=
  fun {R H what₂} N A i => continuous_iotaOQ R H what₂ N A i

end GlobalTheory.CoeffEmbedding
