import Mathlib
import GroundTheory.GlobalFields.HasseNorm

namespace GroundTheory.Automorphic

open Module TensorProduct

section QuadAlg

variable {R : Type*} [CommRing R]

theorem algebraNorm_quadraticAlgebra (a : R) (z : QuadraticAlgebra R a 0) :
    Algebra.norm R z = z.re ^ 2 - a * z.im ^ 2 := by
  rw [Algebra.norm_apply]
  have : Algebra.lmul R (QuadraticAlgebra R a 0) z =
      DistribSMul.toLinearMap R (QuadraticAlgebra R a 0) z := LinearMap.ext fun w => rfl
  rw [this, QuadraticAlgebra.det_toLinearMap_eq_norm, QuadraticAlgebra.norm_def]
  ring

end QuadAlg

section BaseChange

variable {L : Type*} [Field L] (d : L) (R : Type*) [CommRing R] [Algebra L R]

theorem algebraMap_quadraticAlgebra_apply (x : L) :
    algebraMap L (QuadraticAlgebra R (algebraMap L R d) 0) x = ⟨algebraMap L R x, 0⟩ := rfl

omit [Algebra L R] in
theorem quadraticAlgebra_re_one (a : R) : (1 : QuadraticAlgebra R a 0).re = 1 := rfl

omit [Algebra L R] in
theorem quadraticAlgebra_im_one (a : R) : (1 : QuadraticAlgebra R a 0).im = 0 := rfl

def omegaRoot : {u : QuadraticAlgebra R (algebraMap L R d) 0 //
    u * u = d • 1 + (0 : L) • u} :=
  ⟨QuadraticAlgebra.omega, by
    rw [QuadraticAlgebra.omega_mul_omega_eq_mk]
    ext <;> simp [Algebra.smul_def, algebraMap_quadraticAlgebra_apply]⟩

noncomputable def quadMap : QuadraticAlgebra L d 0 →ₐ[L] QuadraticAlgebra R (algebraMap L R d) 0 :=
  QuadraticAlgebra.lift (omegaRoot d R)

theorem quadMap_apply (z : QuadraticAlgebra L d 0) :
    quadMap d R z = ⟨algebraMap L R z.re, algebraMap L R z.im⟩ := by
  simp only [quadMap, QuadraticAlgebra.lift_apply_apply, omegaRoot]
  ext <;> simp [Algebra.smul_def, algebraMap_quadraticAlgebra_apply]

noncomputable def quadTensorHom :
    R ⊗[L] QuadraticAlgebra L d 0 →ₐ[R] QuadraticAlgebra R (algebraMap L R d) 0 :=
  Algebra.TensorProduct.lift (Algebra.ofId R _) (quadMap d R) (fun _ _ => Commute.all _ _)

theorem quadTensorHom_tmul (r : R) (z : QuadraticAlgebra L d 0) :
    quadTensorHom d R (r ⊗ₜ z) = ⟨r * algebraMap L R z.re, r * algebraMap L R z.im⟩ := by
  simp only [quadTensorHom, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, quadMap_apply]
  ext <;> simp [QuadraticAlgebra.algebraMap_eq]

noncomputable def quadTensorInv (z : QuadraticAlgebra R (algebraMap L R d) 0) :
    R ⊗[L] QuadraticAlgebra L d 0 :=
  z.re ⊗ₜ 1 + z.im ⊗ₜ QuadraticAlgebra.omega

theorem quadTensorHom_inv (z : QuadraticAlgebra R (algebraMap L R d) 0) :
    quadTensorHom d R (quadTensorInv d R z) = z := by
  simp only [quadTensorInv, map_add, quadTensorHom_tmul]
  ext <;> simp [quadraticAlgebra_re_one, quadraticAlgebra_im_one]

theorem quadTensorInv_hom (z : R ⊗[L] QuadraticAlgebra L d 0) :
    quadTensorInv d R (quadTensorHom d R z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp [quadTensorInv]
  | tmul r q =>
    rw [quadTensorHom_tmul, quadTensorInv]
    dsimp only
    have hq : q = q.re • (1 : QuadraticAlgebra L d 0) + q.im • QuadraticAlgebra.omega := by
      ext <;> simp [quadraticAlgebra_re_one, quadraticAlgebra_im_one]
    conv_rhs => rw [hq]
    have h1 : ∀ c : L, r * algebraMap L R c = c • r := fun c => by
      rw [Algebra.smul_def, mul_comm]
    rw [TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul, h1, h1,
      TensorProduct.smul_tmul', TensorProduct.smul_tmul']
  | add x y hx hy =>
    have hadd : quadTensorInv d R (quadTensorHom d R (x + y)) =
        quadTensorInv d R (quadTensorHom d R x) + quadTensorInv d R (quadTensorHom d R y) := by
      simp only [map_add, quadTensorInv, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
        TensorProduct.add_tmul]
      abel
    rw [hadd, hx, hy]

noncomputable def quadTensorEquiv :
    R ⊗[L] QuadraticAlgebra L d 0 ≃ₐ[R] QuadraticAlgebra R (algebraMap L R d) 0 :=
  AlgEquiv.ofBijective (quadTensorHom d R)
    ⟨Function.LeftInverse.injective (quadTensorInv_hom d R),
      Function.RightInverse.surjective (quadTensorHom_inv d R)⟩

theorem quadTensorEquiv_tmul (r : R) (z : QuadraticAlgebra L d 0) :
    quadTensorEquiv d R (r ⊗ₜ z) = ⟨r * algebraMap L R z.re, r * algebraMap L R z.im⟩ :=
  quadTensorHom_tmul d R r z

end BaseChange

section Bridge

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.SemiLocal
open scoped NumberField.LiesOver

variable {L : Type*} [Field L] [NumberField L] (d : L) [Fact (∀ r : L, r ^ 2 ≠ d + 0 * r)]

omit [Fact (∀ r : L, r ^ 2 ≠ d + 0 * r)] in

instance numberField_quadraticAlgebra {a b : L} [Fact (∀ r : L, r ^ 2 ≠ a + b * r)] :
    NumberField (QuadraticAlgebra L a b) where
  to_charZero := inferInstance
  to_finiteDimensional := Module.Finite.trans L (QuadraticAlgebra L a b)

omit [NumberField L] in
theorem norm_tensor_quadratic (R : Type*) [CommRing R] [Algebra L R]
    (z : R ⊗[L] QuadraticAlgebra L d 0) :
    Algebra.norm R z = (quadTensorEquiv d R z).re ^ 2 -
      algebraMap L R d * (quadTensorEquiv d R z).im ^ 2 := by
  rw [← Algebra.norm_eq_of_algEquiv (quadTensorEquiv d R) z, algebraNorm_quadraticAlgebra]

theorem mem_range_finiteLocalNorm_iff (w : HeightOneSpectrum (𝓞 L))
    (β : (w.adicCompletion L)ˣ) :
    β ∈ (IdeleNorm.finiteLocalNorm (QuadraticAlgebra L d 0) w).range ↔
      ∃ x y : w.adicCompletion L, x ^ 2 - algebraMap L _ d * y ^ 2 = β := by
  set Lw := w.adicCompletion L
  set e1 := SemiLocal.tensorEquiv (QuadraticAlgebra L d 0) w
  have hN : ∀ z : Lw ⊗[L] QuadraticAlgebra L d 0,
      Algebra.norm Lw z = ∏ u, Algebra.norm Lw (e1 z u) := by
    intro z
    rw [← Algebra.norm_eq_of_algEquiv e1 z, norm_pi]
  constructor
  · rintro ⟨y, rfl⟩
    set z := e1.symm (fun u => (y u : _))
    refine ⟨(quadTensorEquiv d Lw z).re, (quadTensorEquiv d Lw z).im, ?_⟩
    rw [← norm_tensor_quadratic, hN, IdeleNorm.coe_finiteLocalNorm]
    simp only [z, AlgEquiv.apply_symm_apply]
    rfl
  · rintro ⟨x, y, hxy⟩
    set z := (quadTensorEquiv d Lw).symm ⟨x, y⟩
    have hz : Algebra.norm Lw z = β := by
      rw [norm_tensor_quadratic]
      simpa [z] using hxy
    have hne : ∀ u, e1 z u ≠ 0 := by
      intro u hu
      have : Algebra.norm Lw z = 0 := by
        rw [hN]
        exact Finset.prod_eq_zero (Finset.mem_univ u) (by rw [hu, Algebra.norm_zero])
      exact β.ne_zero (hz ▸ this)
    refine ⟨fun u => Units.mk0 (e1 z u) (hne u), Units.ext ?_⟩
    rw [IdeleNorm.coe_finiteLocalNorm, ← hz, hN]
    rfl

theorem mem_range_infiniteLocalNorm_iff (w : InfinitePlace L) (β : (w.Completion)ˣ) :
    β ∈ (IdeleNorm.infiniteLocalNorm (QuadraticAlgebra L d 0) w).range ↔
      ∃ x y : w.Completion, x ^ 2 - algebraMap L _ d * y ^ 2 = β := by
  classical
  set Lw := w.Completion
  set e1 := InfinitePlace.tensorPiEquiv (L := QuadraticAlgebra L d 0) w
  have hN : ∀ z : Lw ⊗[L] QuadraticAlgebra L d 0,
      Algebra.norm Lw z = ∏ u : w.placesOver (QuadraticAlgebra L d 0),
        Algebra.norm Lw (e1 z u) := fun z => InfinitePlace.norm_tensor_eq_prod w z
  constructor
  · rintro ⟨y, rfl⟩
    set z := e1.symm (fun u => (y u : _))
    refine ⟨(quadTensorEquiv d Lw z).re, (quadTensorEquiv d Lw z).im, ?_⟩
    rw [← norm_tensor_quadratic, hN, IdeleNorm.coe_infiniteLocalNorm]
    simp only [z, AlgEquiv.apply_symm_apply]
    rfl
  · rintro ⟨x, y, hxy⟩
    set z := (quadTensorEquiv d Lw).symm ⟨x, y⟩
    have hz : Algebra.norm Lw z = β := by
      rw [norm_tensor_quadratic]
      simp only [z, AlgEquiv.apply_symm_apply]
      exact hxy
    have hne : ∀ u, e1 z u ≠ 0 := by
      intro u hu
      have : Algebra.norm Lw z = 0 := by
        rw [hN]
        exact Finset.prod_eq_zero (Finset.mem_univ u) (by rw [hu, Algebra.norm_zero])
      exact β.ne_zero (hz ▸ this)
    refine ⟨fun u => Units.mk0 (e1 z u) (hne u), Units.ext ?_⟩
    rw [IdeleNorm.coe_infiniteLocalNorm, ← hz, hN]
    rfl

end Bridge

section HasseNorm

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.SemiLocal Filter

universe u

variable {L : Type u} [Field L] [NumberField L]

theorem exists_sq_sub_mul_sq_iff_forall_local {d β : L} (hd : ∀ r : L, r ^ 2 ≠ d) (hβ : β ≠ 0) :
    (∃ x y : L, x ^ 2 - d * y ^ 2 = β) ↔
      (∀ w : HeightOneSpectrum (𝓞 L), ∃ x y : w.adicCompletion L,
          x ^ 2 - algebraMap L _ d * y ^ 2 = algebraMap L _ β) ∧
        ∀ w : InfinitePlace L, ∃ x y : w.Completion,
          x ^ 2 - algebraMap L _ d * y ^ 2 = algebraMap L _ β := by
  have : Fact (∀ r : L, r ^ 2 ≠ d + 0 * r) := ⟨by simpa using hd⟩
  have h2 : Module.finrank L (QuadraticAlgebra L d 0) = 2 := QuadraticAlgebra.finrank_eq_two d 0
  have key := exists_norm_eq_iff_forall_local_of_finrank_eq_two (K := L)
    (L := QuadraticAlgebra L d 0) h2 hβ
  have hl : (∃ x y : L, x ^ 2 - d * y ^ 2 = β) ↔
      ∃ z : QuadraticAlgebra L d 0, Algebra.norm L z = β := by
    constructor
    · rintro ⟨x, y, h⟩
      exact ⟨⟨x, y⟩, by rw [algebraNorm_quadraticAlgebra]; exact h⟩
    · rintro ⟨z, h⟩
      exact ⟨z.re, z.im, by rw [← algebraNorm_quadraticAlgebra]; exact h⟩
  rw [hl, key]
  refine and_congr (forall_congr' fun w => ?_) (forall_congr' fun w => ?_)
  · rw [mem_range_finiteLocalNorm_iff, IdeleGroup.coe_finiteProj_diagonal, Units.val_mk0]
    exact Iff.rfl
  · rw [mem_range_infiniteLocalNorm_iff, IdeleGroup.coe_infiniteProj_diagonal]
    simp

theorem eventually_exists_sq_sub_mul_sq {d β : L} (hd : ∀ r : L, r ^ 2 ≠ d) (hβ : β ≠ 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 L) in cofinite, ∃ x y : w.adicCompletion L,
      x ^ 2 - algebraMap L _ d * y ^ 2 = algebraMap L _ β := by
  have : Fact (∀ r : L, r ^ 2 ≠ d + 0 * r) := ⟨by simpa using hd⟩
  filter_upwards [IdeleNorm.eventually_map_integerUnitsOver_eq (K := L)
      (L := QuadraticAlgebra L d 0),
    IdeleNorm.eventually_finiteProj_mem (IdeleGroup.diagonal L (Units.mk0 β hβ))] with w hw hβw
  rw [← hw] at hβw
  obtain ⟨y, -, hy⟩ := Subgroup.mem_map.1 hβw
  have hmem : IdeleGroup.finiteProj w (IdeleGroup.diagonal L (Units.mk0 β hβ)) ∈
      (IdeleNorm.finiteLocalNorm (QuadraticAlgebra L d 0) w).range := ⟨y, hy⟩
  rwa [mem_range_finiteLocalNorm_iff, IdeleGroup.coe_finiteProj_diagonal, Units.val_mk0] at hmem

end HasseNorm

end GroundTheory.Automorphic
