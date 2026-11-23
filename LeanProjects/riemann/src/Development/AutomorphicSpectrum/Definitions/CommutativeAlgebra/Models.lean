import Mathlib
import GroundTheory.PAdicHodge.FiniteFlat
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder

namespace GlobalTheory.CompanionTheory.Ar.BT

open GroundTheory.PAdicHodge

variable {R : Type} [CommRing R] {T : Type} [CommGroup T]

noncomputable def secPt (G : FiniteFlatGroupScheme.{0, 0} R) {A : Subalgebra R (T → R)} (e : G.H ≃ₐ[R] A) (t : T) :
    G.Points R :=
  WithConv.toConv ((evalAt A t).comp e.toAlgHom)

def Models (G : FiniteFlatGroupScheme.{0, 0} R) (A : Subalgebra R (T → R)) (e : G.H ≃ₐ[R] A) : Prop :=
  ∀ s t, secPt G e (s * t) = secPt G e s * secPt G e t

end GlobalTheory.CompanionTheory.Ar.BT
