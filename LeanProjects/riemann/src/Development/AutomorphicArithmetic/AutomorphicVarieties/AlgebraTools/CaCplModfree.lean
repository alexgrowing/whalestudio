import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IsCplAtSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplFlat
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FinQuotAnn
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FlatnessPrecompleteProducts

open IsLocalRing UpperTheory.V.AlgebraTools

private theorem mult_operator_shifts_twist {Λ R B M : Type} [CommRing Λ] [CommRing R] [Algebra Λ R]
    [AddCommGroup B] [Module R B] [Module Λ B] [IsScalarTower Λ R B]
    [AddCommGroup M] [Module R M] [Module Λ M] [IsScalarTower Λ R M]
    [Module.Flat R B] [Module.Flat Λ M] : Module.Flat Λ (TensorProduct R B M) := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ f hf
  have h1 : Function.Injective (TensorProduct.AlgebraTensorModule.lTensor R M f) :=
    Module.Flat.lTensor_preserves_injective_linearMap f hf
  have h2 : Function.Injective
      (LinearMap.lTensor B (TensorProduct.AlgebraTensorModule.lTensor R M f)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ h1
  have h3 : ∀ x, TensorProduct.AlgebraTensorModule.assoc Λ R R B M N'
        (LinearMap.lTensor (TensorProduct R B M) f x)
      = LinearMap.lTensor B (TensorProduct.AlgebraTensorModule.lTensor R M f)
        (TensorProduct.AlgebraTensorModule.assoc Λ R R B M N x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul y n =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
      | tmul b m => simp
  intro x y hxy
  apply (TensorProduct.AlgebraTensorModule.assoc Λ R R B M N).injective
  apply h2
  rw [← h3, ← h3, hxy]

private theorem fin_of_killed {L B N : Type} [CommRing L] [CommRing B] [Algebra L B]
    [AddCommGroup N] [Module B N] [Module L N] [IsScalarTower L B N] [Module.Finite B N]
    (J : Ideal B) [Module.Finite L (B ⧸ J)] (hJ : Module.IsTorsionBySet B N J) :
    Module.Finite L N := by
  letI : Module (B ⧸ J) N := hJ.module
  haveI : IsScalarTower B (B ⧸ J) N := hJ.isScalarTower
  haveI : IsScalarTower L (B ⧸ J) N := hJ.isScalarTower
  haveI : Module.Finite (B ⧸ J) N := Module.Finite.of_restrictScalars_finite B _ _
  exact Module.Finite.trans (B ⧸ J) N

private theorem fin_quot_ann {Λ R M : Type} [CommRing Λ] [IsNoetherianRing Λ] [CommRing R]
    [Algebra Λ R] [AddCommGroup M] [Module R M] [Module Λ M] [IsScalarTower Λ R M]
    [Module.Finite Λ M] : Module.Finite Λ (R ⧸ Module.annihilator R M) :=
  _root_.UpperTheory.Reformulated.B.Qi2b.fin_quot_ann

theorem UpperTheory.V.AlgebraTools.IsCplAt.finite_free_baseChange :
    ∀ (Λ R : Type) [CommRing Λ] [IsNoetherianRing Λ] [CommRing R] [IsNoetherianRing R] [Algebra Λ R]
      (p : Ideal Λ) (q : Ideal R) (L B : Type) [CommRing L] [IsLocalRing L] [CommRing B] [IsLocalRing B]
      [Algebra Λ L] [Algebra R B] [Algebra L B] [Algebra Λ B] [IsScalarTower Λ R B] [IsScalarTower Λ L B]
      (M : Type) [AddCommGroup M] [Module R M] [Module Λ M] [IsScalarTower Λ R M] [Module.Finite Λ M] [Module.Flat Λ M],
      IsCplAt Λ p L → IsCplAt R q B → q.comap (algebraMap Λ R) = p →
      Module.Finite L (TensorProduct R B M) ∧ Module.Free L (TensorProduct R B M) :=
  _root_.UpperTheory.Reformulated.B.FlatnessPrecompleteProducts.finite_free_baseChange
