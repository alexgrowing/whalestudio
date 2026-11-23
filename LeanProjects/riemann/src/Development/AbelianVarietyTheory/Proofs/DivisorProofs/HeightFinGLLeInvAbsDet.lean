import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LocPoly
import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Height
open NumberField IsDedekindDomain GlobalTheory.HenQ
open GlobalTheory.CuspRep (GA Af finGL)

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.HenQ

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem finGL_apply (k : GL (Fin n) (Af K)) (a b : Fin n) :
    ((finGL K n k : GA K n) : Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) a b =
      (1 : Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) a b
        - GlobalTheory.CuspRep.sFin K ((1 : Matrix (Fin n) (Fin n) (Af K)) a b)
        + GlobalTheory.CuspRep.sFin K ((k : Matrix (Fin n) (Fin n) (Af K)) a b) := rfl

theorem sFin_fst (x : Af K) : (GlobalTheory.CuspRep.sFin K x).1 = 0 := rfl

end GlobalTheory.HenQ

namespace GlobalTheory.HenQ

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

end GlobalTheory.HenQ
