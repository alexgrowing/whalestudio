import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero

set_option autoImplicit false

noncomputable section

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv

namespace GlobalTheory

namespace PDiv

namespace CocycleSum

theorem four {M N : Type} [CommMonoid M] [AddCommGroup N] (c : M → M → N)
    (h : ∀ x y z, c y z - c (x * y) z + c x (y * z) - c x y = 0) (hs : ∀ x y, c x y = c y x)
    (a b a' b' : M) :
    c (a * b) (a' * b') = c a a' + c b b' + (c (a * a') (b * b') - c a b - c a' b') := by
  have h1 := h a b (a' * b')
  have h2 := h a a' (b * b')
  have h3 := h a' b' b
  rw [show b * (a' * b') = a' * (b * b') from mul_left_comm _ _ _] at h1
  rw [show b' * b = b * b' from mul_comm _ _, hs (a' * b') b, hs b' b] at h3
  rw [← sub_eq_zero]
  have e : c (a * b) (a' * b') - (c a a' + c b b' + (c (a * a') (b * b') - c a b - c a' b')) =
      -(c b (a' * b') - c (a * b) (a' * b') + c a (a' * (b * b')) - c a b) +
      (c a' (b * b') - c (a * a') (b * b') + c a (a' * (b * b')) - c a a') -
      (c b b' - c b (a' * b') + c a' (b * b') - c a' b') := by abel
  rw [e, h1, h2, h3]
  simp

variable {R A X : Type} [CommRing R] [CommRing A] [CommRing X] [Bialgebra R A] [Algebra R X]

def val (x y : WithConv (A →ₐ[R] X)) : A ⊗[R] A →ₐ[R] X :=
  Algebra.TensorProduct.lift x.ofConv y.ofConv fun _ _ => .all ..

@[simp] theorem val_tmul (x y : WithConv (A →ₐ[R] X)) (a b : A) :
    val x y (a ⊗ₜ b) = x.ofConv a * y.ofConv b := rfl

theorem mul_apply (x y : WithConv (A →ₐ[R] X)) (a : A) :
    (x * y).ofConv a = val x y (comul a) := by
  rw [val]
  exact AlgHom.convMul_apply x y a

theorem lift_cobTwo (x y z : WithConv (A →ₐ[R] X)) (c : A ⊗[R] A) :
    Algebra.TensorProduct.lift x.ofConv (val y z) (fun _ _ => .all ..) (cobTwo R A c) =
      val y z c - val (x * y) z c + val x (y * z) c - val x y c := by
  have hA : ∀ (t : A ⊗[R] A) (b : A),
      Algebra.TensorProduct.lift x.ofConv (val y z) (fun _ _ => .all ..)
        (TensorProduct.assoc R A A A (t ⊗ₜ b)) = val x y t * z.ofConv b := by
    intro t b
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a a' => simp [mul_assoc]
    | add u v hu hv => simp only [TensorProduct.add_tmul, map_add, hu, hv, add_mul]
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [cobTwo_apply]
    simp only [map_sub, map_add, TensorProduct.mk_apply, LinearMap.rTensor_tmul,
      LinearMap.lTensor_tmul, LinearMap.flip_apply, Algebra.TensorProduct.lift_tmul, val_tmul, hA,
      mul_apply, map_one, one_mul, mul_one]
  | add u v hu hv =>
    simp only [map_add, hu, hv]
    abel

theorem val_comm (x y : WithConv (A →ₐ[R] X)) (c : A ⊗[R] A) :
    val x y (TensorProduct.comm R A A c) = val y x c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rw [TensorProduct.comm_tmul, val_tmul, val_tmul, mul_comm]
  | add u v hu hv => simp only [map_add, hu, hv]

theorem val_push {Y : Type} [CommRing Y] [Algebra R Y] (u : X →ₐ[R] Y)
    (x y : WithConv (A →ₐ[R] X)) (c : A ⊗[R] A) :
    val (ptsPush A u x) (ptsPush A u y) c = u (val x y c) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp only [val_tmul, ptsPush_ofConv, AlgHom.comp_apply, map_mul]
  | add u v hu hv => simp only [map_add, hu, hv]

variable {B : Type} [CommRing B] [Bialgebra R B]

theorem val_include (x y : WithConv (A →ₐ[R] B)) (c : A ⊗[R] A) :
    val (ptsPush A (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B) x)
      (ptsPush A (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B) y) c =
      TensorProduct.map x.ofConv.toLinearMap y.ofConv.toLinearMap c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [val_tmul, ptsPush_ofConv, AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      one_mul, TensorProduct.map_tmul, AlgHom.toLinearMap_apply]
  | add u v hu hv => simp only [map_add, hu, hv]

theorem include_mul (f : A →ₐc[R] B) :
    ptsPush A (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B) (toConv (f : A →ₐ[R] B)) *
      ptsPush A (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B) (toConv (f : A →ₐ[R] B)) =
      ptsPush A (comulAlgHom R B) (toConv (f : A →ₐ[R] B)) := by
  apply WithConv.ext
  ext a
  rw [mul_apply, val_include]
  simp only [ptsPush_ofConv, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
  exact CoalgHomClass.map_comp_comul_apply f a

end CocycleSum

open CocycleSum in

theorem pullTwo_convMul {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Bialgebra R A]
    [Bialgebra R B] [IsCocomm R A] (f g : A →ₐc[R] B) (c : A ⊗[R] A) (hc : c ∈ symCocycles R A) :
    pullbackTwo (toConv f * toConv g).ofConv c = pullbackTwo f c + pullbackTwo g c +
      cobOne R B (LinearMap.mul' R B
        (TensorProduct.map (f : A →ₗ[R] B) (g : A →ₗ[R] B) c)) := by
  obtain ⟨hc2, hcs⟩ := mem_symCocycles.1 hc
  have hv : ∀ (x y : WithConv (A →ₐ[R] B)) (t : A ⊗[R] A), val x y t =
      LinearMap.mul' R B (TensorProduct.map x.ofConv.toLinearMap y.ofConv.toLinearMap t) := by
    intro x y t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add u v hu hv => simp only [map_add, hu, hv]
  have key := four (M := WithConv (A →ₐ[R] B ⊗[R] B)) (fun x y => val x y c)
    (fun x y z => (lift_cobTwo x y z c).symm.trans (by rw [hc2, map_zero]))
    (fun x y => by rw [← val_comm, hcs])
    (ptsPush A (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B) (toConv (f : A →ₐ[R] B)))
    (ptsPush A (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B) (toConv (g : A →ₐ[R] B)))
    (ptsPush A (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B) (toConv (f : A →ₐ[R] B)))
    (ptsPush A (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B) (toConv (g : A →ₐ[R] B)))
  rw [← map_mul (ptsPush A (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B)),
    ← map_mul (ptsPush A (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B)),
    include_mul f, include_mul g, val_include, val_include, val_include, val_push, val_push,
    val_push] at key
  have hl : ∀ h : A →ₐc[R] B, (h : A →ₗ[R] B) = (h : A →ₐ[R] B).toLinearMap := fun _ => rfl
  have hfg : ((toConv f * toConv g).ofConv : A →ₐ[R] B) =
      (toConv (f : A →ₐ[R] B) * toConv (g : A →ₐ[R] B)).ofConv :=
    congrArg WithConv.ofConv (BialgHom.toAlgHom_convMul (toConv f) (toConv g))
  have hv' : LinearMap.mul' R B (TensorProduct.map (f : A →ₗ[R] B) (g : A →ₗ[R] B) c) =
      val (toConv (f : A →ₐ[R] B)) (toConv (g : A →ₐ[R] B)) c := by
    rw [hv, hl, hl]
  unfold pullbackTwo
  rw [hl, hfg, key, cobOne_apply, hv', Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, hl, hl]
  rfl

end PDiv

end GlobalTheory
