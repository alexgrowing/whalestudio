import Formalism.FrobeniusContraction.Statement

noncomputable section

namespace Formalism.WachCohomologyFacts.PPs

open Formalism.WachCohomologyFacts

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A]

lemma p_eq_pow (B : Base O A) (s : ℕ) : B.p s = (B.φ ^ s) B.q := by
  unfold Base.p
  induction s with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', AlgHom.mul_apply, Function.iterate_succ_apply', ih]

lemma p_eq (B : Base O A) (s : ℕ) : B.p s = (B.φ ^ s) B.X + (B.ℓ : A) := by
  rw [p_eq_pow, Base.q, map_add, map_natCast]

end Formalism.WachCohomologyFacts.PPs

namespace Formalism.WachCohomologyFacts

open Formalism.WachCohomologyFacts.PPs

end Formalism.WachCohomologyFacts
