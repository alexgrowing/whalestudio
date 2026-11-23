import Mathlib
import GroundTheory.AutomorphicForms.QuadraticConj

namespace GroundTheory.Automorphic

open Module Matrix

section MatrixGroup

variable {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] [DecidableEq ι]

def unitaryGroupMatrix (s : A →+* A) (H : Matrix ι ι A) : Subgroup (GL ι A) where
  carrier := {g | ((g : Matrix ι ι A).map s)ᵀ * H * g = H}
  one_mem' := by
    simp [Matrix.map_one _ (map_zero s) (map_one s)]
  mul_mem' {g k} hg hk := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Units.val_mul, Matrix.map_mul, transpose_mul]
    calc _ = ((k : Matrix ι ι A).map s)ᵀ *
          ((((g : Matrix ι ι A).map s)ᵀ * H * g) * k) := by simp only [Matrix.mul_assoc]
      _ = H := by rw [hg, ← Matrix.mul_assoc, hk]
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at *
    have h1 : ((g : Matrix ι ι A).map s) * ((↑g⁻¹ : Matrix ι ι A).map s) = 1 := by
      rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero s) (map_one s)]
    calc ((↑g⁻¹ : Matrix ι ι A).map s)ᵀ * H * ↑g⁻¹
        = ((↑g⁻¹ : Matrix ι ι A).map s)ᵀ * (((g : Matrix ι ι A).map s)ᵀ * H * g) * ↑g⁻¹ := by
          rw [hg]
      _ = (((g : Matrix ι ι A).map s) * ((↑g⁻¹ : Matrix ι ι A).map s))ᵀ * H *
          ((g : Matrix ι ι A) * ↑g⁻¹) := by
          rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = H := by rw [h1, Units.mul_inv, transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem mem_unitaryGroupMatrix {s : A →+* A} {H : Matrix ι ι A} {g : GL ι A} :
    g ∈ unitaryGroupMatrix s H ↔ ((g : Matrix ι ι A).map s)ᵀ * H * g = H := Iff.rfl

theorem isUnit_det_of_unitary (s : A →+* A) {H : Matrix ι ι A} (hH : IsUnit H.det)
    {M : Matrix ι ι A} (hM : (M.map s)ᵀ * H * M = H) : IsUnit M.det := by
  have hd := congrArg Matrix.det hM
  have hs : (M.map s).det = s M.det := (RingHom.map_det s M).symm
  rw [det_mul, det_mul, det_transpose, hs] at hd
  have h2 : M.det * s M.det = 1 := by
    apply hH.mul_left_cancel
    linear_combination hd
  exact IsUnit.of_mul_eq_one _ h2

theorem exists_mem_unitaryGroupMatrix_iff (s : A →+* A) {H : Matrix ι ι A} (hH : IsUnit H.det)
    (M : Matrix ι ι A) :
    (∃ g ∈ unitaryGroupMatrix s H, (g : Matrix ι ι A) = M) ↔ (M.map s)ᵀ * H * M = H := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact hg
  · intro hM
    exact ⟨nonsingInvUnit M (isUnit_det_of_unitary s hH hM), hM, rfl⟩

def IsHermitianFor (s : A →+* A) (H : Matrix ι ι A) : Prop := (H.map s)ᵀ = H

end MatrixGroup

variable (F E : Type*) [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]

noncomputable abbrev conjHom : E →+* E := (conj F E).toAlgHom.toRingHom

variable (V : Type*) [AddCommGroup V] [Module E V]

structure HermitianForm where

  toSesq : V →ₛₗ[conjHom F E] V →ₗ[E] E

  isSymm : toSesq.IsSymm

  nonsingular : Function.Bijective toSesq

variable {F E V}

namespace HermitianForm

def unitaryGroup (h : HermitianForm F E V) : Subgroup (V ≃ₗ[E] V) where
  carrier := {g | ∀ x y, h.toSesq (g x) (g y) = h.toSesq x y}
  one_mem' := fun _ _ => rfl
  mul_mem' {a b} ha hb x y := by
    change h.toSesq (a (b x)) (a (b y)) = _
    rw [ha, hb]
  inv_mem' {a} ha x y := by
    change h.toSesq (a.symm x) (a.symm y) = _
    conv_rhs => rw [← a.apply_symm_apply x, ← a.apply_symm_apply y]
    rw [ha]

theorem mem_unitaryGroup {h : HermitianForm F E V} {g : V ≃ₗ[E] V} :
    g ∈ h.unitaryGroup ↔ ∀ x y, h.toSesq (g x) (g y) = h.toSesq x y := Iff.rfl

end HermitianForm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def gram (B : V →ₛₗ[conjHom F E] V →ₗ[E] E) (v : Basis ι E V) : Matrix ι ι E :=
  fun i j => B (v i) (v j)

omit [Fintype ι] [DecidableEq ι] in
theorem gram_apply (B : V →ₛₗ[conjHom F E] V →ₗ[E] E) (v : Basis ι E V) (i j : ι) :
    gram B v i j = B (v i) (v j) := rfl

omit [DecidableEq ι] in

theorem sesq_eq_sum (B : V →ₛₗ[conjHom F E] V →ₗ[E] E) (v : Basis ι E V) (x y : V) :
    B x y = ∑ i, ∑ j, conj F E (v.repr x i) * gram B v i j * v.repr y j := by
  conv_lhs => rw [← v.sum_repr x, ← v.sum_repr y]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul,
    smul_eq_mul, Finset.mul_sum, gram_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_toAlgHom]
  ring

omit [Fintype ι] [DecidableEq ι] in

theorem isHermitianFor_gram (h : HermitianForm F E V) (v : Basis ι E V) :
    IsHermitianFor (conjHom F E) (gram h.toSesq v) := by
  ext i j
  simp only [transpose_apply, map_apply, gram_apply]
  exact h.isSymm.eq (v j) (v i)

theorem isUnit_det_gram (h : HermitianForm F E V) (v : Basis ι E V) :
    IsUnit (gram h.toSesq v).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← vecMul_surjective_iff_isUnit]
  intro w
  obtain ⟨x, hx⟩ := h.nonsingular.2 (v.constr E w)
  refine ⟨fun i => conj F E (v.repr x i), ?_⟩
  ext j
  have hxj : h.toSesq x (v j) = w j := by rw [hx, Basis.constr_basis]
  rw [← hxj, sesq_eq_sum h.toSesq v]
  simp only [vecMul, dotProduct, Basis.repr_self, Finsupp.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem sesq_apply_map_basis (B : V →ₛₗ[conjHom F E] V →ₗ[E] E) (v : Basis ι E V)
    (g : V →ₗ[E] V) (i j : ι) :
    B (g (v i)) (g (v j)) =
      (((LinearMap.toMatrix v v g).map (conjHom F E))ᵀ * gram B v * LinearMap.toMatrix v v g)
        i j := by
  rw [sesq_eq_sum B v]
  simp only [Matrix.mul_apply, transpose_apply, map_apply, LinearMap.toMatrix_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem mem_unitaryGroup_iff_toMatrix (h : HermitianForm F E V) (v : Basis ι E V)
    (g : V ≃ₗ[E] V) :
    g ∈ h.unitaryGroup ↔
      ((LinearMap.toMatrix v v (g : V →ₗ[E] V)).map (conjHom F E))ᵀ * gram h.toSesq v *
        LinearMap.toMatrix v v (g : V →ₗ[E] V) = gram h.toSesq v := by
  constructor
  · intro hg
    ext i j
    rw [← sesq_apply_map_basis]
    exact hg _ _
  · intro hM x y
    have key : (h.toSesq.comp (g : V →ₗ[E] V)).compl₂ (g : V →ₗ[E] V) = h.toSesq := by
      refine LinearMap.ext_basis v v fun i j => ?_
      have := congrFun (congrFun hM i) j
      rw [← sesq_apply_map_basis] at this
      simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
      simpa [gram_apply] using this
    exact LinearMap.congr_fun₂ key x y

noncomputable def autEquivGL (v : Basis ι E V) : (V ≃ₗ[E] V) ≃* GL ι E :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv E V).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv v).toRingEquiv.toMulEquiv)

theorem autEquivGL_apply (v : Basis ι E V) (g : V ≃ₗ[E] V) :
    (autEquivGL v g : Matrix ι ι E) = LinearMap.toMatrix v v (g : V →ₗ[E] V) := by
  simp [autEquivGL]
  rfl

noncomputable def unitaryGroupEquivMatrix (h : HermitianForm F E V) (v : Basis ι E V) :
    h.unitaryGroup ≃* unitaryGroupMatrix (conjHom F E) (gram h.toSesq v) where
  toFun g := ⟨autEquivGL v g, by
    rw [mem_unitaryGroupMatrix, autEquivGL_apply]
    exact (mem_unitaryGroup_iff_toMatrix h v g).1 g.2⟩
  invFun m := ⟨(autEquivGL v).symm m, by
    rw [mem_unitaryGroup_iff_toMatrix h v, ← autEquivGL_apply, MulEquiv.apply_symm_apply]
    exact m.2⟩
  left_inv g := Subtype.ext (by simp)
  right_inv m := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    change autEquivGL v ((a : V ≃ₗ[E] V) * b) = autEquivGL v a * autEquivGL v b
    exact map_mul _ _ _)

theorem unitaryGroupEquivMatrix_apply (h : HermitianForm F E V) (v : Basis ι E V)
    (g : h.unitaryGroup) :
    ((unitaryGroupEquivMatrix h v g : GL ι E) : Matrix ι ι E) =
      LinearMap.toMatrix v v ((g : V ≃ₗ[E] V) : V →ₗ[E] V) :=
  autEquivGL_apply v g

end GroundTheory.Automorphic
