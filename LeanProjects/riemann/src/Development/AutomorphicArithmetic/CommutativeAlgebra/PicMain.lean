import Development.AutomorphicArithmetic.CommutativeAlgebra.TorsorRelSelfIffExistsCoboundary
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsInvertibleModuleOfLocallyTrivialCocycle
import Development.AutomorphicArithmetic.CommutativeAlgebra.InvertibleModuleEquivOfSameCocycle
import Development.AutomorphicArithmetic.CommutativeAlgebra.RelAddTensorProductOfRel

open CategoryTheory TensorProduct

namespace UpperTheory.PicD.Data
variable (P : Data)

theorem Rel.congr {A : Type} [CommRing A] {z : P.S1.obj (CommRingCat.of A)} {M M' : Type} [AddCommGroup M] [Module A M]
    [AddCommGroup M'] [Module A M'] (h : P.Rel z M) (e : M ≃ₗ[A] M') : P.Rel z M' := by
  obtain ⟨C, i1, i2, hff, het, w, g, t, ht⟩ := h
  refine ⟨C, i1, i2, hff, het, w, g, t ∘ₗ e.symm.toLinearMap, ?_⟩
  have hfun : ⇑(LinearMap.liftBaseChange C (t ∘ₗ e.symm.toLinearMap)) =
      ⇑(LinearMap.liftBaseChange C t) ∘ ⇑(LinearEquiv.baseChange A C M' M e.symm) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c m => simp [LinearMap.liftBaseChange_tmul]
    | add x y hx hy =>
      simp only [Function.comp_apply, map_add] at hx hy ⊢
      rw [hx, hy]
  refine Triv.mk ht.dw ht.hg (fun m => ht.ht (e.symm m)) ?_
  rw [hfun]
  exact ht.bij.comp (LinearEquiv.bijective _)

theorem main (A : Type) [CommRing A] (Z : AddSubgroup (P.S1.obj (CommRingCat.of A))) (hZ : ∀ z ∈ Z, P.LocEx z) :
    ∃ φ : Z →+ Additive (CommRing.Pic A), ∀ z : Z, φ z = 0 ↔ ∃ y, P.dd A y = z.1 := by
  classical
  have hex : ∀ z : Z, ∃ N : CommRing.Pic A, P.Rel z.1 N := by
    intro z
    obtain ⟨M, i1, i2, hinv, hrel⟩ := UpperTheory.exists_invertibleModule_of_locallyTrivial_cocycle P A z.1 (hZ z.1 z.2)
    exact ⟨CommRing.Pic.mk A M, Rel.congr P hrel (CommRing.Pic.mk.linearEquiv A M).symm⟩
  choose f hf using hex
  have hone : ∀ z : Z, f z = 1 ↔ P.Rel z.1 A := by
    intro z
    rw [← CommRing.Pic.mk_eq_self (M := f z), CommRing.Pic.mk_eq_one_iff]
    constructor
    · rintro ⟨e⟩
      exact Rel.congr P (hf z) e
    · intro hA
      exact UpperTheory.invertibleModule_equiv_of_same_cocycle P A z.1 _ _ (hf z) hA
  have hmul : ∀ x y : Z, f (x + y) = f x * f y := by
    intro x y
    rw [CommRing.Pic.mul_eq_tensor]
    exact ((CommRing.Pic.mk_eq_iff).mpr
      (UpperTheory.invertibleModule_equiv_of_same_cocycle P A (x + y).1 _ _ (UpperTheory.rel_add_tensorProduct_of_rel P A x.1 y.1 _ _ (hf x) (hf y)) (hf (x + y)))).symm
  refine ⟨{ toFun := fun z => Additive.ofMul (f z), map_zero' := ?_, map_add' := ?_ }, ?_⟩
  · show Additive.ofMul (f 0) = Additive.ofMul 1
    congr 1
    exact (hone 0).mpr ((UpperTheory.torsorRel_self_iff_exists_coboundary P A _).mpr ⟨0, by simp⟩)
  · intro x y
    show Additive.ofMul (f (x + y)) = Additive.ofMul (f x * f y)
    rw [hmul]
  · intro z
    show Additive.ofMul (f z) = 0 ↔ _
    rw [ofMul_eq_zero, hone, UpperTheory.torsorRel_self_iff_exists_coboundary]

end UpperTheory.PicD.Data
