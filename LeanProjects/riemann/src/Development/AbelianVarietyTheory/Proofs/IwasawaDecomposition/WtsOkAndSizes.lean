import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseDataEmbeddingConj
import Formalism.LocalToGlobal.Columns.BaseLemmas

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

namespace GlobalTheory.Mem

theorem wts_ok_and_sizes :
    ∀ (B : Base) (X : PreX B.toPre), B.wts.Ok ∧ Sizes (B.primes X) B.wts X.a :=
  fun B X => ⟨B.wts_isOk, B.primes_sizes X⟩

end GlobalTheory.Mem
