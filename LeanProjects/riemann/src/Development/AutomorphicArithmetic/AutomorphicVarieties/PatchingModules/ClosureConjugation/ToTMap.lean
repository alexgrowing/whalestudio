import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDetMap
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem toT_map {B G : Type} [CommRing B] [Group G] (C : Type) [CommRing C] [Algebra B C]
    (y : MonoidAlgebra B G) : toT B G C (MonoidAlgebra.mapRingHom G (algebraMap B C) y) = 1 ⊗ₜ y := by
  have h := toT_ofT (A := B) (S := C) (1 ⊗ₜ y)
  rwa [ofT_tmul, one_smul] at h

theorem UpperTheory.V.Pa.tens :
    ∀ {n : ℕ} {B G E : Type} [CommRing B] [Group G] [Ring E] [Algebra B E] (D : GDet n B G) (DE : Det n B E) (π : MonoidAlgebra B G →ₐ[B] E) (C : Type) [CommRing C] [Algebra B C], Function.Surjective π → DE.pull π = D.toDet → ∃ ι : MonoidAlgebra C G →ₐ[C] C ⊗[B] E, Function.Surjective ι ∧ (∀ y, ι (MonoidAlgebra.mapRingHom G (algebraMap B C) y) = 1 ⊗ₜ π y) ∧ (∀ y, ι y = 0 ↔ y ∈ TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G (algebraMap B C) '' {z | π z = 0})) ∧ (DE.baseChange C).pull ι = (D.map (algebraMap B C)).toDet := by
  intro n B G E _ _ _ _ D DE π C _ _ hπ hD
  let m : C ⊗[B] MonoidAlgebra B G →ₐ[C] C ⊗[B] E := Algebra.TensorProduct.map (AlgHom.id C C) π
  have hm : ∀ x, m x = π.toLinearMap.lTensor C x := fun x => by
    induction x with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul s y => rfl
  have h2 : ∀ y, m (toT B G C (MonoidAlgebra.mapRingHom G (algebraMap B C) y)) = 1 ⊗ₜ π y := fun y => by
    rw [toT_map]; rfl
  refine ⟨m.comp (toT B G C), fun w => ?_, h2, fun y => ⟨fun hy => ?_, fun hy => ?_⟩, ?_⟩
  · obtain ⟨x, hx⟩ := LinearMap.lTensor_surjective C (g := π.toLinearMap) hπ w
    exact ⟨ofT B G C x, by rw [AlgHom.comp_apply, toT_ofT, hm, hx]⟩
  · rw [AlgHom.comp_apply, hm] at hy
    obtain ⟨x, hx⟩ := (lTensor_exact C (LinearMap.exact_subtype_ker_map π.toLinearMap) hπ _).1 hy
    rw [← ofT_toT (A := B) y, ← hx]
    clear hx
    induction x with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add]; exact add_mem ha hb
    | tmul s z =>
      rw [LinearMap.lTensor_tmul, ofT_tmul, Algebra.smul_def]
      exact TwoSidedIdeal.mul_mem_left _ _ _ (TwoSidedIdeal.subset_span ⟨z, z.2, rfl⟩)
  · have hle : TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G (algebraMap B C) '' {z | π z = 0}) ≤
        TwoSidedIdeal.ker (m.comp (toT B G C)) := by
      rw [TwoSidedIdeal.span_le]
      rintro _ ⟨z, hz, rfl⟩
      refine (TwoSidedIdeal.mem_ker _).2 ((h2 z).trans ?_)
      rw [show π z = 0 from hz, TensorProduct.tmul_zero]
    exact (TwoSidedIdeal.mem_ker _).1 (hle hy)
  · rw [d_toDet_map, ← hD]
    refine Det.ext' fun S _ _ x => ?_
    letI : Algebra B S := ((algebraMap C S).comp (algebraMap B C)).toAlgebra
    haveI : IsScalarTower B C S := .of_algebraMap_eq fun _ => rfl
    have h : Det.cancel B E C S (Algebra.TensorProduct.map (AlgHom.id S S) (m.comp (toT B G C)) x) =
        Algebra.TensorProduct.map (AlgHom.id S S) π (Det.cancel B (MonoidAlgebra B G) C S
          (Algebra.TensorProduct.map (AlgHom.id S S) (toT B G C) x)) := by
      induction x with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | tmul s y =>
        rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.comp_apply]
        generalize toT B G C y = w
        induction w with
        | zero => simp
        | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]
        | tmul c z => simp [m, Det.cancel_tmul]
    exact congrArg (DE.D S) h
