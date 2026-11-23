import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HodgeCoh

set_option autoImplicit false

namespace GlobalTheory.HodgeCoh
open GlobalTheory.CechDR

variable {k : Type} [CommRing k] {X : Scheme.{0}}

theorem formPull_id (s : X ⟶ Sp k) (j : ℕ) (U : X.Opens) (x : OmU s U j) :
    formPull (f := 𝟙 X) (Category.id_comp s) U j x = x :=
  SemiHom.mOm_id _ (fun _ ↦ rfl) x

theorem omegaPull_id (s : X ⟶ Sp k) (j : ℕ) :
    omegaPull (f := 𝟙 X) (Category.id_comp s) j =
      (Scheme.Modules.pushforwardId X).inv.app (Omega s j) := by
  refine (Equiv.symm_apply_eq _).2 ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_unit _ _ _ _).symm
  ext U x
  exact congrArg ((toOmega s j).app U).hom (formPull_id s j U.unop x)

theorem hodgePull_id (s : X ⟶ Sp k) (j q : ℕ) (x : hodgeH s j q) :
    hodgePull (f := 𝟙 X) (Category.id_comp s) j q x = x := by
  letI := algΓ s
  apply (cohOn.toH' (Omega s j) ⊤ q).injective
  refine (cohOn.toH'_pull (appTop_algebraMap (Category.id_comp s))
    (omegaPull (Category.id_comp s) j) (le_refl ((𝟙 X) ⁻¹ᵁ ⊤)) (n := q) x).trans ?_
  rw [omegaPull_id]
  exact (SheafPull.pull_id (X := X.toTopCat) (𝟙 ((toAbSheaf X).obj (Omega s j))) q
    (homOfLE (le_refl ⊤)) _).trans (by rw [SheafLES.map_id]; exact SheafLES.res_id _ _ _)

end GlobalTheory.HodgeCoh
