import Mathlib
import Formalism.LocalToGlobal.Divisibility.DefGroup

noncomputable section

open Matrix

namespace GlobalTheory.FlatConj

def gaussGL {k : Type} [Field k] [Fintype k] [DecidableEq k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r : ℕ) : ℂ :=
  ∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) * ψ (Matrix.trace (x : Matrix (Fin r) (Fin r) k))

variable {E : Type} [Field E] [NumberField E]

def resField (PP : Formalism.L2.DIV.Pl E) : Field (Formalism.L2.DIV.kP PP) :=
  haveI := PP.isMaximal
  Ideal.Quotient.field PP.asIdeal

def resFintype (PP : Formalism.L2.DIV.Pl E) : Fintype (Formalism.L2.DIV.kP PP) :=
  haveI : Finite (Formalism.L2.DIV.kP PP) := Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
  Fintype.ofFinite _

def gaussP (PP : Formalism.L2.DIV.Pl E) (ψ : AddChar (Formalism.L2.DIV.kP PP) ℂ) (ξ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (r : ℕ) : ℂ :=
  @gaussGL (Formalism.L2.DIV.kP PP) (resField PP) (resFintype PP) (Classical.decEq _) ψ ξ r

end GlobalTheory.FlatConj
