import Mathlib

open TensorProduct PiTensorProduct

namespace GlobalTheory

noncomputable section

universe u v w

variable {A : Type u} [CommRing A] {σ : Type w} [Fintype σ] [DecidableEq σ] {X : σ → Type v}
  [∀ s, CommRing (X s)] [∀ s, Algebra A (X s)] {S : Type*} [CommRing S] [Algebra A S]

def piTensorLift (f : ∀ s, X s →ₐ[A] S) : (⨂[A] s, X s) →ₐ[A] S :=
  liftAlgHom ((MultilinearMap.mkPiAlgebra A σ S).compLinearMap fun s => (f s).toLinearMap)
    (by simp) (fun x y => by simp [Finset.prod_mul_distrib])

omit [DecidableEq σ] in

@[simp] theorem piTensorLift_tprod (f : ∀ s, X s →ₐ[A] S) (x : ∀ s, X s) :
    piTensorLift f (tprod A x) = ∏ s, f s (x s) := by
  refine (PiTensorProduct.lift.tprod x).trans ?_
  simp

@[simp] theorem piTensorLift_comp_single (f : ∀ s, X s →ₐ[A] S) (s : σ) :
    (piTensorLift f).comp (singleAlgHom s) = f s := by
  ext x
  rw [AlgHom.comp_apply, singleAlgHom_apply, piTensorLift_tprod,
    Finset.prod_eq_single s (fun t _ ht => by simp [Pi.mulSingle_eq_of_ne ht]) (by simp)]
  simp

theorem piTensorLift_single (f : ∀ s, X s →ₐ[A] S) (s : σ) (x : X s) :
    piTensorLift f (singleAlgHom s x) = f s x := congr($(piTensorLift_comp_single f s) x)

variable (A X S) in

@[simps] def piTensorHomEquiv : ((⨂[A] s, X s) →ₐ[A] S) ≃ ∀ s, X s →ₐ[A] S where
  toFun f s := f.comp (singleAlgHom s)
  invFun := piTensorLift
  left_inv _ := PiTensorProduct.algHom_ext fun s => by simp
  right_inv f := funext fun s => by simp

theorem piTensor_induction
    (P : ∀ (B : Type (max u v w)) [CommRing B] [Algebra A B], Prop)
    (equiv : ∀ (B C : Type (max u v w)) [CommRing B] [Algebra A B] [CommRing C] [Algebra A C],
      (B ≃ₐ[A] C) → P B → P C)
    (base : ∀ (B : Type (max u v w)) [CommRing B] [Algebra A B], (A ≃ₐ[A] B) → P B)
    (σ : Type w) [Fintype σ] :
    ∀ (X : σ → Type v) [∀ s, CommRing (X s)] [∀ s, Algebra A (X s)],
      (∀ s (B : Type (max u v w)) [CommRing B] [Algebra A B], P B → P (B ⊗[A] X s)) →
      P (⨂[A] s, X s) := by
  classical
  refine Fintype.induction_empty_option (P := fun σ _ =>
    ∀ (X : σ → Type v) [∀ s, CommRing (X s)] [∀ s, Algebra A (X s)],
      (∀ s (B : Type (max u v w)) [CommRing B] [Algebra A B], P B → P (B ⊗[A] X s)) →
      P (⨂[A] s, X s)) ?_ ?_ ?_ σ
  · intro α β _ e ih X _ _ h
    have := Fintype.ofEquiv β e.symm
    refine equiv _ _ (AlgEquiv.ofAlgHom (piTensorLift fun a => singleAlgHom (e a))
      (piTensorLift (e.piCongrLeft (fun b => X b →ₐ[A] ⨂[A] a, X (e a))
        fun a => singleAlgHom (A := fun a => X (e a)) a)) ?_ ?_)
      (ih (fun a => X (e a)) fun a => h (e a))
    · refine PiTensorProduct.algHom_ext fun b => ?_
      obtain ⟨a, rfl⟩ := e.surjective b
      simp [AlgHom.comp_assoc]
    · refine PiTensorProduct.algHom_ext fun a => ?_
      simp [AlgHom.comp_assoc]
  · intro X _ _ _
    exact base _ (AlgEquiv.ofAlgHom (Algebra.ofId _ _) (piTensorLift fun s => s.elim)
      (PiTensorProduct.algHom_ext fun s => s.elim) (Subsingleton.elim _ _))
  · intro α _ ih X _ _ h
    refine equiv _ _ (AlgEquiv.ofAlgHom
      (Algebra.TensorProduct.lift (piTensorLift fun a => singleAlgHom (some a)) (singleAlgHom none)
        fun _ _ => Commute.all _ _)
      (piTensorLift fun o => match o with
        | none => Algebra.TensorProduct.includeRight
        | some a => Algebra.TensorProduct.includeLeft.comp
            (singleAlgHom (A := fun a => X (some a)) a)) ?_ ?_)
      (h none _ (ih (fun a => X (some a)) fun a => h (some a)))
    · refine PiTensorProduct.algHom_ext fun o => ?_
      rw [AlgHom.comp_assoc, piTensorLift_comp_single]
      cases o with
      | none => simp
      | some a => simp [← AlgHom.comp_assoc]
    · refine Algebra.TensorProduct.ext (PiTensorProduct.algHom_ext fun a => ?_) ?_
      · simp [AlgHom.comp_assoc]
      · ext x
        simp [piTensorLift_single, -singleAlgHom_apply]

end

end GlobalTheory
