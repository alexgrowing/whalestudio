import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicProperties
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.abelianSchemeProperClosureData_basic_properties : ∀ C : Core, IsSeparated C.GG.hom ∧ LocallyOfFiniteType C.GG.hom ∧ QuasiCompact C.GG.hom ∧ IsIntegral C.G.toScheme ∧ Flat (C.GG.hom ≫ C.π) ∧ Flat (C.P.hom ≫ C.π) ∧ IsOpenImmersion C.a ∧ IsPullback C.a C.A.hom C.GG.hom C.U.ι ∧ Set.range C.a = C.GG.hom ⁻¹' C.U ∧ IsNoetherian C.Z ∧ IsNoetherian C.P.left ∧ IsDominant C.GG.hom ∧ ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) (τ : C.Test y), C.Cl y ∧ CharZero τ.V ∧ IsSemiAbelian τ.H := by
  first | exact @GlobalTheory.ZJ.core_basic | exact GlobalTheory.ZJ.core_basic | (intros; apply GlobalTheory.ZJ.core_basic <;> assumption)
