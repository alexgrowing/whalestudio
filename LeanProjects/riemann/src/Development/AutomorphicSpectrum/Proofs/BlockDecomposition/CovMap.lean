import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.UnipotentTateFunctionalEquation

noncomputable section

open MeasureTheory Matrix Ad3 Ad3.K Ad3.K.LC Ad3.K.LC.C

namespace GlobalTheory.CompanionTheory.CoVC

abbrev E : Type := Fin 2 → ℂ

def mk (a b : E) : M22 := fun i => ![a i, b i]

def hOf (κ : M22) (v t : ℂ) : M22 := Matrix.of.symm (Matrix.of κ * !![0, v; 1, t])

def xOf (v t : ℂ) : E := ![-t / v, 1 / v]

def covMap (w : M22 × ℂ × E) : ℂ × (M22 × E) :=
  (w.2.2 0 - w.2.1, hOf w.1 w.2.1 (w.2.2 1), xOf w.2.1 (w.2.2 1))

end GlobalTheory.CompanionTheory.CoVC
