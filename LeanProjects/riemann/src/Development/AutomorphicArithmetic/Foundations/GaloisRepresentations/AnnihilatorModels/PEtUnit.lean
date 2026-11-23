import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.etUnit_of :
    EtOfUnit := by
  intro l R S B _ _ _ _ _ h hl
  have hl' : IsUnit (algebraMap R B (l : R)) := by simpa using hl
  letI : Algebra (Localization.Away (l : R)) B :=
    (IsLocalization.Away.lift (S := Localization.Away (l : R)) (l : R) hl').toAlgebra
  haveI : IsScalarTower R (Localization.Away (l : R)) B :=
    IsScalarTower.of_algebraMap_eq fun r =>
      (IsLocalization.Away.lift_eq (S := Localization.Away (l : R)) (l : R) hl' r).symm
  exact Algebra.Etale.of_equiv
    (Algebra.TensorProduct.cancelBaseChange R (Localization.Away (l : R)) B B S)
