import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.FieldTheory.Finiteness

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

theorem UpperTheory.card_dual_residueField_eq_card_of_maximalIdeal_smul_eq_zero :
    ∀ {O N : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [AddCommGroup N] [Module O N] [Finite N], (∀ a ∈ maximalIdeal O, ∀ x : N, a • x = 0) → Nat.card (N →ₗ[O] ResidueField O) = Nat.card N := by
  intro O N _ _ _ _ _ _ h
  classical
  have hM : Module.IsTorsionBySet O N (maximalIdeal O) := fun x a => h a a.2 x
  letI : Module (ResidueField O) N := hM.module
  haveI : IsScalarTower O (ResidueField O) N := hM.isScalarTower
  have e := LinearMap.extendScalarsOfSurjectiveEquiv (R := O) (S := ResidueField O) (M := N)
    (N := ResidueField O) IsLocalRing.residue_surjective
  rw [Nat.card_congr e.toEquiv]
  let b := Module.Free.chooseBasis (ResidueField O) N
  exact (Nat.card_congr b.toDualEquiv.toEquiv).symm
