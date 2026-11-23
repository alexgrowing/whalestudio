import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem coeff_eq_mk_rootT {l : ℕ} [Fact l.Prime] (e : Per.Fl l) (n : ℕ) :
    PreTilt.coeff n e = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)}) (rootT e n) := by
  have h2 := PreTilt.mk_untilt_eq_coeff_zero (((frobeniusEquiv (Per.Fl l) l).symm^[n]) e)
  have h3 := PreTilt.coeff_iterate_frobeniusEquiv_symm 0 n e
  rw [zero_add] at h3
  rw [← h3, ← h2]
  rfl

theorem eps_coeff : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (n : ℕ),
    PreTilt.coeff n C.ε = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)}) (rootT C.ε n) :=
  fun _ _ C n => coeff_eq_mk_rootT C.ε n

end GlobalTheory.MemLoc
