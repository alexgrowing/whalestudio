import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTangent
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.ProjOrigin

open ProjSpace

theorem chartι_mem_chart_iff (R : Type) [CommRing R] (N : ℕ) (i : Fin (N + 1)) (j : {j // j ≠ i})
    (p : Sp (MvPolynomial {j // j ≠ i} R)) :
    chartι R N i p ∈ chart R N j.1 ↔ (X j : MvPolynomial {j // j ≠ i} R) ∉ p.asIdeal := by
  have h := Proj.awayι_preimage_basicOpen (grading R N) (X_mem R N i) one_pos (X_mem R N j.1) one_pos
  have e : awayToPoly R N i (HomogeneousLocalization.Away.isLocalizationElem (X_mem R N i) (X_mem R N j.1))
      = X j := by
    refine (awayToPoly_mk R N i _ _ _).trans ?_
    rw [pow_one, dehom_X_of_ne]
  rw [← e]
  exact (congrArg (spMap (awayToPoly R N i) p ∈ ·) h).to_iff

def origin {R K : Type} [CommRing R] [Field K] (N : ℕ) (φ : R →+* K) : Sp K ⟶ PSpace R N :=
  spMap (eval₂Hom φ fun _ : {j : Fin (N + 1) // j ≠ 0} => 0) ≫ chartι R N 0

end GlobalTheory.ProjOrigin
