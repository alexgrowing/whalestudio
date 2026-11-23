import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SmGL.Exponents

section Bool

variable {X : Bool → Type} [∀ x, AddCommGroup (X x)] [∀ x, Module ℂ (X x)]

def boolPair (v : X false) (w : X true) : ∀ x, X x
  | false => v
  | true => w

def boolMulti : MultilinearMap ℂ X (X false ⊗[ℂ] X true) :=
  MultilinearMap.mk' (fun x => x false ⊗ₜ[ℂ] x true)
    (fun m i x y => by cases i <;> simp [TensorProduct.add_tmul, TensorProduct.tmul_add])
    (fun m i c x => by cases i <;> simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul])

theorem boolPair_eq_right (v : X false) (w w' : X true) :
    boolPair v w = Function.update (boolPair v w') true w := by
  funext x; cases x <;> simp [boolPair]

theorem boolPair_eq_left (v v' : X false) (w : X true) :
    boolPair v w = Function.update (boolPair v' w) false v := by
  funext x; cases x <;> simp [boolPair]

def boolBilin : X false →ₗ[ℂ] X true →ₗ[ℂ] PiTensorProduct ℂ X :=
  LinearMap.mk₂ ℂ (fun v w => PiTensorProduct.tprod ℂ (boolPair v w))
    (fun v v' w => by
      rw [boolPair_eq_left (v + v') 0, boolPair_eq_left v 0, boolPair_eq_left v' 0,
        MultilinearMap.map_update_add])
    (fun c v w => by
      rw [boolPair_eq_left (c • v) 0, boolPair_eq_left v 0, MultilinearMap.map_update_smul])
    (fun v w w' => by
      rw [boolPair_eq_right v (w + w') 0, boolPair_eq_right v w 0, boolPair_eq_right v w' 0,
        MultilinearMap.map_update_add])
    (fun c v w => by
      rw [boolPair_eq_right v (c • w) 0, boolPair_eq_right v w 0, MultilinearMap.map_update_smul])

def boolTensorEquiv : PiTensorProduct ℂ X ≃ₗ[ℂ] X false ⊗[ℂ] X true :=
  LinearEquiv.ofLinear (PiTensorProduct.lift boolMulti) (TensorProduct.lift boolBilin)
    (by
      ext v w
      simp [boolBilin, boolMulti, boolPair])
    (by
      ext x
      simp only [boolBilin, boolMulti, LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
        PiTensorProduct.lift.tprod, MultilinearMap.mk'_apply, TensorProduct.lift.tmul,
        LinearMap.mk₂_apply, LinearMap.id_apply]
      congr 1
      funext i
      cases i <;> rfl)

theorem boolTensorEquiv_tprod (x : ∀ i, X i) :
    boolTensorEquiv (PiTensorProduct.tprod ℂ x) = x false ⊗ₜ[ℂ] x true := by
  simp [boolTensorEquiv, boolMulti]

end Bool

def piTensorTwoEquiv {R a b V W : Type} [CommRing R] [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL a R) V) (π₂ : Representation ℂ (GL b R) W) :
    (piTensor (twoRep π₁ π₂)).Equiv
      ((extTensor π₁ π₂).comp (leviTwo R a b).symm.toMonoidHom) :=
  .mk (boolTensorEquiv (X := Two V W)) fun g => by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    show boolTensorEquiv (X := Two V W) (piTensor (twoRep π₁ π₂) g (PiTensorProduct.tprod ℂ x)) =
      extTensor π₁ π₂ ((leviTwo R a b).symm g) (boolTensorEquiv (X := Two V W) (PiTensorProduct.tprod ℂ x))
    rw [piTensor_tprod, boolTensorEquiv_tprod, boolTensorEquiv_tprod]
    exact (extTensor_tmul π₁ π₂ ((leviTwo R a b).symm g) (x false) (x true)).symm

theorem prod₂_equiv_multiProd (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type)
    [AddCommGroup W] [Module ℂ W] (π₁ : Representation ℂ (GL (Fin r) k) V)
    (π₂ : Representation ℂ (GL (Fin t) k) W) :
    Nonempty ((prod₂ π₁ π₂).Equiv (multiProd (two (stdSum (rfl : r + t = r + t))) (twoRep π₁ π₂))) :=
  ⟨(LocGL.parIndEquiv (two (stdSum (rfl : r + t = r + t))) (piTensorTwoEquiv π₁ π₂)).symm⟩

end GlobalTheory.SmGL.Exponents
