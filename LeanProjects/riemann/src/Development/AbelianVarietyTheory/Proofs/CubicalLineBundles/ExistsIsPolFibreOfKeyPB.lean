import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.KeyFibre

theorem eq_dualMapR_of_algebraMap {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R')
    (F : DualNumber R →+* DualNumber R') (h : ∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a))
    (he : F DualNumber.eps = DualNumber.eps) : F = Chart.dualMapR f := by
  refine RingHom.ext fun x => ?_
  have e : x = algebraMap R _ x.fst + algebraMap R _ x.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [e, map_add, map_mul, h, h, he]
  ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_isPolFibre_of_keyPB : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (x : KeyIn R) (x' : KeyIn R'), KeyPB x' x f → ∃ (φ : x'.P.A.left ⟶ x.P.A.left) (hg : x'.P.g = x.P.g), IsPolFibre f x.P x'.P φ ∧ ∀ i, IsVecOver f φ (x.v (i.cast hg)) (x'.v i) := by
  intro R R' _ _ f x x' h
  obtain ⟨φ, he, w, hg, F, hφ, hw, h1, h2, hF, hε, hv⟩ := h
  refine ⟨φ, hg, ⟨hg, hφ, LBIso.symm ⟨w, hw⟩⟩, fun i => ?_⟩
  have := hv i
  rw [eq_dualMapR_of_algebraMap f F hF hε] at this
  exact this

end GlobalTheory.KeyFibre
