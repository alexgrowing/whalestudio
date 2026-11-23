import Formalism.PeriodIntegrals.NablaSpans.ExpansionCoeffValuationGe

noncomputable section

open scoped BigOperators
open Classical

namespace CutKW

def minorX (R : Type) [CommRing R] (N p : ℕ) (I : Fin p ↪o Fin N) : MvPolynomial (ℕ × Fin N) R :=
  Matrix.det (Matrix.of fun i k : Fin p => MvPolynomial.X ((i : ℕ), I k))

def nablaSpan (R : Type) [CommRing R] (N : ℕ) (nu : YoungDiagram) :
    Submodule R (MvPolynomial (ℕ × Fin N) R) :=
  Submodule.span R (Set.range fun I : ∀ c : Fin (nu.rowLen 0), Fin (nu.colLen c) ↪o Fin N =>
    ∏ c : Fin (nu.rowLen 0), minorX R N (nu.colLen c) (I c))

def MinorProdSpanHasCompl : Prop :=
  ∀ (R : Type) [CommRing R] (N : ℕ) (nu : YoungDiagram),
    ∃ Cm : Submodule R (MvPolynomial (ℕ × Fin N) R), IsCompl (nablaSpan R N nu) Cm

def KWsb : Prop := MinorProdSpanHasCompl → KW

end CutKW
