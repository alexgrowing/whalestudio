import Development.AutomorphicArithmetic.CommutativeAlgebra.PicData
open CategoryTheory TensorProduct UpperTheory.PicD

namespace UpperTheory.PicD

section
variable {A C : Type} [CommRing A] [CommRing C] [Algebra A C]

private theorem smul_eq_left_inclusion (b : C) (x : C ⊗[A] C) : b • x = i1 A C b * x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, mul_add, hx, hy]
  | tmul p q => simp [smul_tmul']

private theorem act_eq (x : C ⊗[A] C) :
    GlobalTheory.FlatDescent.act A C C x = Algebra.TensorProduct.lmul' A x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul p q => simp

private theorem lTensor_theta (g x : C ⊗[A] C) :
    ((theta g).restrictScalars A).lTensor C x = c12 A C x * c23 A C g := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, add_mul, hx, hy]
  | tmul p q =>
    simp [smul_eq_left_inclusion, Algebra.TensorProduct.tmul_mul_tmul]

private theorem lTensor_mk (x : C ⊗[A] C) :
    (TensorProduct.mk A C C 1).lTensor C x = c13 A C x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul p q => simp

private theorem isDescentDatum_theta (g : C ⊗[A] C)
    (hc : c12 A C g * c23 A C g = c13 A C g) (hu : Algebra.TensorProduct.lmul' A g = (1 : C)) :
    GlobalTheory.FlatDescent.IsDescentDatum (theta g) := by
  constructor
  · intro b
    rw [theta_apply, map_smul, act_eq, hu]
    simp
  · intro b
    rw [theta_apply, lTensor_theta, lTensor_mk, smul_eq_left_inclusion, map_mul, map_mul, mul_assoc, hc]
    congr 1

end

end UpperTheory.PicD

theorem UpperTheory.exists_invertibleModule_of_locallyTrivial_cocycle :
    ∀ (P : Data) (A : Type) [CommRing A] (z : P.S1.obj (CommRingCat.of A)), P.LocEx z →
        ∃ (M : Type) (_ : AddCommGroup M) (_ : Module A M), Module.Invertible A M ∧ P.Rel z M := by
  intro P A _ z hz
  obtain ⟨C, _, _, hff, het, w, hw⟩ := hz
  have hdx : P.dd _ (P.r0 (i2 A C).toRingHom w - P.r0 (i1 A C).toRingHom w) = 0 := by
    have hcomp : (i2 A C).toRingHom.comp (algebraMap A C) = (i1 A C).toRingHom.comp (algebraMap A C) :=
      RingHom.ext fun a => ((i2 A C).commutes a).trans ((i1 A C).commutes a).symm
    rw [map_sub, P.diff_mapDegZero, P.diff_mapDegZero, hw, P.mapDegOne_comp, P.mapDegOne_comp, hcomp, sub_self]
  obtain ⟨g, hg⟩ := (P.dd_eq_zero _).1 hdx
  have q1 : (c12 A C).toRingHom.comp (i1 A C).toRingHom = (c13 A C).toRingHom.comp (i1 A C).toRingHom := by
    ext b <;> simp
  have q2 : (c12 A C).toRingHom.comp (i2 A C).toRingHom = (c23 A C).toRingHom.comp (i1 A C).toRingHom := by
    ext b <;> simp
  have q3 : (c13 A C).toRingHom.comp (i2 A C).toRingHom = (c23 A C).toRingHom.comp (i2 A C).toRingHom := by
    ext b <;> simp
  have hcoc : Units.map (c12 A C).toRingHom.toMonoidHom g * Units.map (c23 A C).toRingHom.toMonoidHom g =
      Units.map (c13 A C).toRingHom.toMonoidHom g := by
    apply P.un_injective
    rw [P.un_mul, ← P.mapDegZero_ofUnit, ← P.mapDegZero_ofUnit, ← P.mapDegZero_ofUnit, hg]
    simp only [map_sub, P.mapDegZero_comp]
    rw [q1, q2, q3]
    abel
  have hcount : Units.map (Algebra.TensorProduct.lmul' A (S := C)).toRingHom.toMonoidHom g = 1 := by
    apply P.un_injective
    have hcomp : (Algebra.TensorProduct.lmul' A (S := C)).toRingHom.comp (i2 A C).toRingHom =
        (Algebra.TensorProduct.lmul' A (S := C)).toRingHom.comp (i1 A C).toRingHom := by
      ext b <;> simp
    rw [← P.mapDegZero_ofUnit, hg, P.un_one]
    simp only [map_sub, P.mapDegZero_comp]
    rw [hcomp, sub_self]
  have hdd : GlobalTheory.FlatDescent.IsDescentDatum (theta (g : C ⊗[A] C)) := by
    refine isDescentDatum_theta _ ?_ ?_
    · simpa using congrArg Units.val hcoc
    · simpa using congrArg Units.val hcount
  refine ⟨↥(Mg (g : C ⊗[A] C)), inferInstance, inferInstance, hdd.invertible_invariants, ?_⟩
  exact ⟨C, _, _, hff, het, w, g, (Mg (g : C ⊗[A] C)).subtype,
    ⟨hw, hg, fun m => GlobalTheory.FlatDescent.mem_invariants.1 m.2, hdd.bijective_extend⟩⟩
