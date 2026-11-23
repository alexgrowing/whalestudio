import Mathlib
import GroundTheory.Brauer.CrossedProductIso
import GroundTheory.Brauer.CrossedProductTensor
import GroundTheory.Brauer.BaseChange
import GroundTheory.Brauer.DoubleCentralizer
import GroundTheory.Brauer.Splitting
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Brauer

open Module groupCohomology

open scoped TensorProduct

universe u

namespace CrossedProduct

section Restrict

variable {K E L : Type*} [Field K] [Field E] [Field L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L]

variable (K E) in

def resCocycle (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) : (L ≃ₐ[E] L) × (L ≃ₐ[E] L) → Lˣ :=
  fun p => f (p.1.restrictScalars K, p.2.restrictScalars K)

@[simp]
theorem resCocycle_apply (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) (p : (L ≃ₐ[E] L) × (L ≃ₐ[E] L)) :
    resCocycle K E f p = f (p.1.restrictScalars K, p.2.restrictScalars K) :=
  rfl

theorem isMulCocycle₂_resCocycle {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₂ f) :
    IsMulCocycle₂ (resCocycle K E f) := by
  intro g h j
  exact hf (g.restrictScalars K) (h.restrictScalars K) (j.restrictScalars K)

end Restrict

section Action

variable {K E L : Type*} [Field K] [Field E] [Field L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L]
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₂ f)

variable (E) in

def inclBase : E →ₐ[K] CrossedProduct hf :=
  (incl (hf := hf)).comp (IsScalarTower.toAlgHom K E L)

theorem inclBase_apply (e : E) : inclBase E hf e = incl (algebraMap E L e) :=
  rfl

theorem incl_mul_inclBase (a : L) (e : E) :
    incl a * inclBase E hf e = inclBase E hf e * (incl a : CrossedProduct hf) := by
  rw [inclBase_apply, ← map_mul, mul_comm, map_mul]

theorem u_mul_inclBase (τ : L ≃ₐ[E] L) (e : E) :
    u (τ.restrictScalars K) * inclBase E hf e = inclBase E hf e * (u (τ.restrictScalars K) : CrossedProduct hf) := by
  rw [inclBase_apply, u_mul_incl, AlgEquiv.restrictScalars_apply, AlgEquiv.commutes]

def rightMulEnd (c : CrossedProduct hf) (hc : ∀ e : E, c * inclBase E hf e = inclBase E hf e * c) :
    Module.End E (RightMul (inclBase E hf)) where
  toFun x := RightMul.of _ (x.val * c)
  map_add' x y := add_mul x.val y.val c
  map_smul' e x := by
    change x.val * inclBase E hf e * c = x.val * c * inclBase E hf e
    rw [mul_assoc, ← hc, mul_assoc]

def rightInclHom : L →ₐ[E] (Module.End E (RightMul (inclBase E hf)))ᵐᵒᵖ where
  toFun a := MulOpposite.op (rightMulEnd hf (incl a) (incl_mul_inclBase hf a))
  map_one' := by
    apply MulOpposite.unop_injective
    refine LinearMap.ext fun x => ?_
    change RightMul.of _ (x.val * incl 1) = x
    rw [map_one, mul_one]
    rfl
  map_mul' a b := by
    apply MulOpposite.unop_injective
    refine LinearMap.ext fun x => ?_
    change RightMul.of _ (x.val * incl (a * b)) = RightMul.of _ ((x.val * incl a) * incl b)
    rw [map_mul, mul_assoc]
  map_zero' := by
    apply MulOpposite.unop_injective
    refine LinearMap.ext fun x => ?_
    change RightMul.of _ (x.val * incl 0) = 0
    rw [map_zero, mul_zero]
    rfl
  map_add' a b := by
    apply MulOpposite.unop_injective
    refine LinearMap.ext fun x => ?_
    change RightMul.of _ (x.val * incl (a + b)) = RightMul.of _ (x.val * incl a + x.val * incl b)
    rw [map_add, mul_add]
  commutes' e := by
    apply MulOpposite.unop_injective
    refine LinearMap.ext fun x => ?_
    change RightMul.of _ (x.val * incl (algebraMap E L e)) = e • x
    rfl

def rightSymbol (τ : L ≃ₐ[E] L) : (Module.End E (RightMul (inclBase E hf)))ᵐᵒᵖ :=
  MulOpposite.op (rightMulEnd hf (u (τ.restrictScalars K)) (u_mul_inclBase hf τ))

def rightAction :
    CrossedProduct (isMulCocycle₂_resCocycle (E := E) hf) →ₐ[E]
      (Module.End E (RightMul (inclBase E hf)))ᵐᵒᵖ :=
  lift (rightInclHom hf) (rightSymbol hf)
    (fun σ a => by
      apply MulOpposite.unop_injective
      refine LinearMap.ext fun x => ?_
      change RightMul.of _ ((x.val * u (σ.restrictScalars K)) * incl a) =
        RightMul.of _ ((x.val * incl (σ a)) * u (σ.restrictScalars K))
      rw [mul_assoc, u_mul_incl, mul_assoc]
      rfl)
    (fun σ τ => by
      apply MulOpposite.unop_injective
      refine LinearMap.ext fun x => ?_
      change RightMul.of _ ((x.val * u (σ.restrictScalars K)) * u (τ.restrictScalars K)) =
        RightMul.of _ ((x.val * incl (f (σ.restrictScalars K, τ.restrictScalars K) : L)) *
          u ((σ * τ).restrictScalars K))
      rw [mul_assoc, u_mul_u, mul_assoc]
      rfl)
    (by
      apply MulOpposite.unop_injective
      refine LinearMap.ext fun x => ?_
      change RightMul.of _ (x.val * u ((1 : L ≃ₐ[E] L).restrictScalars K)) =
        RightMul.of _ (x.val * incl (f ((1 : L ≃ₐ[E] L).restrictScalars K,
          (1 : L ≃ₐ[E] L).restrictScalars K) : L))
      exact congrArg (fun y => RightMul.of _ (x.val * y)) (u_one (hf := hf)))

end Action

section Main

variable {K E L : Type u} [Field K] [Field E] [Field L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L] [FiniteDimensional K L] [IsGalois K L]
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₂ f)

def rightActionOp :
    (CrossedProduct (isMulCocycle₂_resCocycle (E := E) hf))ᵐᵒᵖ →ₐ[E]
      Module.End E (RightMul (inclBase E hf)) :=
  (AlgEquiv.opOp E (Module.End E (RightMul (inclBase E hf)))).symm.toAlgHom.comp
    (AlgHom.op (rightAction hf))

end Main

end CrossedProduct

namespace H2mul

section Res

variable (K E L : Type*) [Field K] [Field E] [Field L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L]

def resBase : H2mul (L ≃ₐ[K] L) Lˣ →* H2mul (L ≃ₐ[E] L) Lˣ :=
  mapPair (AlgEquiv.restrictScalarsHom K) (MonoidHom.id Lˣ) (fun _ _ => rfl)

variable {K E L}

end Res

section Brauer

variable {K E L : Type u} [Field K] [Field E] [Field L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L] [FiniteDimensional K L] [IsGalois K L]

end Brauer

end H2mul

end GroundTheory.Brauer
