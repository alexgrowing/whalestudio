import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GeoModel

open AlgebraicGeometry CategoryTheory
open GlobalTheory.CompanionTheory.Ar.SncBase

def SncPts {X : Scheme.{0}} {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (e : ℕ)
    (B : Set (Cpt ξ)) : Prop :=
  ∀ p, Char0 ξ p → ∃ (A : Subalgebra ℚ Ω) (z : Fin e → A) (n : ℕ) (q : Ideal A),
    IsSncPatch (Pts ξ) (regAt ξ '' B) e A z n ∧ q.IsPrime ∧ IsLocAt A q (regAt ξ p)

end GlobalTheory.CompanionTheory.Ar.GeoModel
