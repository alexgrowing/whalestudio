import Mathlib
import Formalism.UnipotentAdelicQuotients.ClassNumberFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormGroupToPadicPointsDegreeOneEqUnitaryPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TC

noncomputable section

open GlobalTheory.LKTrip
open scoped TensorProduct

namespace GlobalTheory.TorLoc

section Defs

variable (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D]
variable (R : Type) [CommRing R] [Algebra ℚ R]

abbrev basR : Module.Basis (Fin (Module.finrank ℚ D)) R (R ⊗[ℚ] D) :=
  Algebra.TensorProduct.basis R (Module.finBasis ℚ D)

abbrev lreg : R ⊗[ℚ] D →ₐ[R] Matrix (Fin (Module.finrank ℚ D)) (Fin (Module.finrank ℚ D)) R :=
  Algebra.leftMulMatrix (basR D R)

def blk0 (z : (R ⊗[ℚ] D) × R) :
    Matrix (Fin (Module.finrank ℚ D) ⊕ Fin 1) (Fin (Module.finrank ℚ D) ⊕ Fin 1) R :=
  Matrix.fromBlocks (lreg D R z.1) 0 0 (Matrix.scalar (Fin 1) z.2)

def blk : (R ⊗[ℚ] D) × R →+* Matrix (Fin (Module.finrank ℚ D + 1)) (Fin (Module.finrank ℚ D + 1)) R where
  toFun z := Matrix.reindexAlgEquiv R R finSumFinEquiv (blk0 D R z)
  map_one' := by
    rw [← map_one (Matrix.reindexAlgEquiv R R (finSumFinEquiv (m := Module.finrank ℚ D) (n := 1)))]
    congr 1
    simp [blk0, Matrix.fromBlocks_one]
  map_mul' z w := by
    rw [← map_mul]
    congr 1
    simp [blk0, Matrix.fromBlocks_multiply]
  map_zero' := by
    rw [← map_zero (Matrix.reindexAlgEquiv R R (finSumFinEquiv (m := Module.finrank ℚ D) (n := 1)))]
    congr 1
    simp [blk0]
  map_add' z w := by
    rw [← map_add]
    congr 1
    simp [blk0, Matrix.fromBlocks_add]

def coordA (X : Matrix (Fin (Module.finrank ℚ D + 1)) (Fin (Module.finrank ℚ D + 1)) R) : R ⊗[ℚ] D :=
  (basR D R).equivFun.symm (fun i => ∑ j, X (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) *
    (basR D R).repr 1 j)

def coordC (X : Matrix (Fin (Module.finrank ℚ D + 1)) (Fin (Module.finrank ℚ D + 1)) R) : R :=
  X (finSumFinEquiv (Sum.inr 0)) (finSumFinEquiv (Sum.inr 0))

theorem coordA_blk (z : (R ⊗[ℚ] D) × R) : coordA D R (blk D R z) = z.1 := by
  have h := Algebra.leftMulMatrix_mulVec_repr (basR D R) z.1 1
  rw [mul_one] at h
  simp only [coordA, blk, blk0, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁]
  have key : (fun i => ∑ j, lreg D R z.1 i j * (basR D R).repr 1 j) = (basR D R).equivFun z.1 := by
    funext i
    have := congrFun h i
    simp only [Matrix.mulVec, dotProduct] at this
    rw [Module.Basis.equivFun_apply, ← this]
  rw [key]
  exact (basR D R).equivFun.symm_apply_apply z.1

theorem coordC_blk (z : (R ⊗[ℚ] D) × R) : coordC D R (blk D R z) = z.2 := by
  simp [coordC, blk, blk0, Matrix.reindexAlgEquiv_apply]

theorem blk_injective : Function.Injective (blk D R) := fun z w h => by
  have h1 := coordA_blk D R z
  have h2 := coordC_blk D R z
  rw [h, coordA_blk] at h1
  rw [h, coordC_blk] at h2
  exact Prod.ext h1.symm h2.symm

end Defs
end GlobalTheory.TorLoc

namespace GlobalTheory.TorLoc

section Nat

variable {D : Type} [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D]
variable {R R' : Type} [CommRing R] [Algebra ℚ R] [CommRing R'] [Algebra ℚ R']

theorem repr_map (f : R →ₐ[ℚ] R') (x : R ⊗[ℚ] D) (k : Fin (Module.finrank ℚ D)) :
    (basR D R').repr (Algebra.TensorProduct.map f (AlgHom.id ℚ D) x) k = f ((basR D R).repr x k) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r m =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.basis_repr_tmul,
      Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem lreg_map (f : R →ₐ[ℚ] R') (a : R ⊗[ℚ] D) :
    lreg D R' (Algebra.TensorProduct.map f (AlgHom.id ℚ D) a) = f.toRingHom.mapMatrix (lreg D R a) := by
  ext i j
  simp only [lreg, Algebra.leftMulMatrix_eq_repr_mul, RingHom.mapMatrix_apply, Matrix.map_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← repr_map f]
  congr 2
  simp [Algebra.TensorProduct.basis_apply]

theorem blk_map (f : R →ₐ[ℚ] R') (z : (R ⊗[ℚ] D) × R) :
    blk D R' (Algebra.TensorProduct.map f (AlgHom.id ℚ D) z.1, f z.2) = f.toRingHom.mapMatrix (blk D R z) := by
  ext i j
  simp only [blk, blk0, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.reindexAlgEquiv_apply,
    Matrix.reindex_apply, Matrix.submatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, lreg_map]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;>
    (try rw [Subsingleton.elim i j]) <;>
    simp [Matrix.fromBlocks_apply₁₁, Matrix.scalar_apply, Matrix.diagonal_apply, apply_ite]

theorem repr_coordA (X : Matrix (Fin (Module.finrank ℚ D + 1)) (Fin (Module.finrank ℚ D + 1)) R)
    (k : Fin (Module.finrank ℚ D)) :
    (basR D R).repr (coordA D R X) k =
      ∑ j, X (finSumFinEquiv (Sum.inl k)) (finSumFinEquiv (Sum.inl j)) * (basR D R).repr 1 j := by
  simp only [coordA]
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

theorem coordA_map (f : R →ₐ[ℚ] R') (X : Matrix (Fin (Module.finrank ℚ D + 1)) (Fin (Module.finrank ℚ D + 1)) R) :
    coordA D R' (f.toRingHom.mapMatrix X) = Algebra.TensorProduct.map f (AlgHom.id ℚ D) (coordA D R X) := by
  apply (basR D R').repr.injective
  ext k
  rw [repr_map, repr_coordA, repr_coordA, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, ← repr_map f]
  have h1 : Algebra.TensorProduct.map f (AlgHom.id ℚ D) (1 : R ⊗[ℚ] D) = 1 := map_one _
  rw [h1]
  rfl

theorem coordC_map (f : R →ₐ[ℚ] R') (X : Matrix (Fin (Module.finrank ℚ D + 1)) (Fin (Module.finrank ℚ D + 1)) R) :
    coordC D R' (f.toRingHom.mapMatrix X) = f (coordC D R X) := rfl

end Nat
end GlobalTheory.TorLoc

namespace GlobalTheory.TorLoc

section Cond

variable {D : Type} [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D)
variable {R R' : Type} [CommRing R] [Algebra ℚ R] [CommRing R'] [Algebra ℚ R']

theorem starT_tmap (f : R →ₐ[ℚ] R') (x : R ⊗[ℚ] D) :
    (starT σ R' (Algebra.TensorProduct.map f (AlgHom.id ℚ D) x)).unop =
      Algebra.TensorProduct.map f (AlgHom.id ℚ D) (starT σ R x).unop := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r m => simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, starT_tmul]
  | add x y hx hy => simp only [map_add, MulOpposite.unop_add, hx, hy]

variable (R) in

def formE (a : R ⊗[ℚ] D) (c : R) : R ⊗[ℚ] D :=
  a * ((1 : R) ⊗ₜ β) * (starT σ R a).unop - algebraMap R (R ⊗[ℚ] D) c * ((1 : R) ⊗ₜ β)

variable (R) in

def commE (a : R ⊗[ℚ] D) : R ⊗[ℚ] D := a * ((1 : R) ⊗ₜ y) - ((1 : R) ⊗ₜ y) * a

theorem formE_map (f : R →ₐ[ℚ] R') (a : R ⊗[ℚ] D) (c : R) :
    Algebra.TensorProduct.map f (AlgHom.id ℚ D) (formE σ β R a c) =
      formE σ β R' (Algebra.TensorProduct.map f (AlgHom.id ℚ D) a) (f c) := by
  simp only [formE, map_sub, map_mul, starT_tmap, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  simp [Algebra.TensorProduct.algebraMap_apply]

theorem commE_map (f : R →ₐ[ℚ] R') (a : R ⊗[ℚ] D) :
    Algebra.TensorProduct.map f (AlgHom.id ℚ D) (commE y R a) =
      commE y R' (Algebra.TensorProduct.map f (AlgHom.id ℚ D) a) := by
  simp only [commE, map_sub, map_mul, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]

variable (R) in

def cond (X : Matrix (Fin (Module.finrank ℚ D + 1)) (Fin (Module.finrank ℚ D + 1)) R) :
    (Fin (Module.finrank ℚ D + 1) × Fin (Module.finrank ℚ D + 1)) ⊕
      (Fin (Module.finrank ℚ D) ⊕ Fin (Module.finrank ℚ D)) → R
  | Sum.inl ij => X ij.1 ij.2 - blk D R (coordA D R X, coordC D R X) ij.1 ij.2
  | Sum.inr (Sum.inl k) => (basR D R).repr (formE σ β R (coordA D R X) (coordC D R X)) k
  | Sum.inr (Sum.inr k) => (basR D R).repr (commE y R (coordA D R X)) k

theorem cond_map (f : R →ₐ[ℚ] R') (X : Matrix (Fin (Module.finrank ℚ D + 1)) (Fin (Module.finrank ℚ D + 1)) R)
    (ω) : f (cond σ β y R X ω) = cond σ β y R' (f.toRingHom.mapMatrix X) ω := by
  rcases ω with ⟨i, j⟩ | k | k
  · have hb := congrFun (congrFun (blk_map f (coordA D R X, coordC D R X)) i) j
    simp only [cond, map_sub, coordA_map, coordC_map, hb]
    rfl
  · simp only [cond, coordA_map, coordC_map, ← formE_map, repr_map]
  · simp only [cond, coordA_map, ← commE_map, repr_map]

theorem cond_zero_iff (X : Matrix (Fin (Module.finrank ℚ D + 1)) (Fin (Module.finrank ℚ D + 1)) R) :
    (∀ ω, cond σ β y R X ω = 0) ↔ X = blk D R (coordA D R X, coordC D R X) ∧
      formE σ β R (coordA D R X) (coordC D R X) = 0 ∧ commE y R (coordA D R X) = 0 := by
  constructor
  · intro h
    refine ⟨Matrix.ext fun i j => sub_eq_zero.1 (h (Sum.inl (i, j))), ?_, ?_⟩
    · exact (basR D R).forall_coord_eq_zero_iff.1 fun k => h (Sum.inr (Sum.inl k))
    · exact (basR D R).forall_coord_eq_zero_iff.1 fun k => h (Sum.inr (Sum.inr k))
  · rintro ⟨h1, h2, h3⟩ ω
    rcases ω with ⟨i, j⟩ | k | k
    · simp only [cond]; rw [← h1, sub_self]
    · simp only [cond, h2, map_zero, Finsupp.zero_apply]
    · simp only [cond, h3, map_zero, Finsupp.zero_apply]

end Cond
end GlobalTheory.TorLoc

namespace GlobalTheory.TorLoc

section Units

variable {D : Type} [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D]
variable {R : Type} [CommRing R] [Algebra ℚ R]

theorem isUnit_of_blk_mul (z : (R ⊗[ℚ] D) × R)
    (Y : Matrix (Fin (Module.finrank ℚ D + 1)) (Fin (Module.finrank ℚ D + 1)) R) (h : blk D R z * Y = 1) :
    IsUnit z.1 ∧ IsUnit z.2 := by
  set Y' := Matrix.reindexAlgEquiv R R (finSumFinEquiv (m := Module.finrank ℚ D) (n := 1)).symm Y with hY'
  have hY : Y = Matrix.reindexAlgEquiv R R finSumFinEquiv Y' := by
    rw [hY']; ext i j; simp [Matrix.reindexAlgEquiv_apply]
  have h0 : blk0 D R z * Y' = 1 := by
    apply (Matrix.reindexAlgEquiv R R (finSumFinEquiv (m := Module.finrank ℚ D) (n := 1))).injective
    rw [map_mul, map_one, ← hY]
    exact h
  rw [← Matrix.fromBlocks_toBlocks Y', blk0, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one,
    Matrix.fromBlocks_inj] at h0
  obtain ⟨h11, -, -, h22⟩ := h0
  simp only [Matrix.zero_mul, add_zero, zero_add] at h11 h22
  constructor
  · set B := Y'.toBlocks₁₁
    set a := z.1
    have hBL : B * lreg D R a = 1 := mul_eq_one_comm.1 h11
    set a' := (basR D R).equivFun.symm (Matrix.mulVec B ⇑((basR D R).repr 1)) with ha'
    have hr : ⇑((basR D R).repr a') = Matrix.mulVec B ⇑((basR D R).repr 1) := by
      funext i
      rw [← Module.Basis.equivFun_apply, ha', LinearEquiv.apply_symm_apply]
    have e1 : a * a' = 1 := by
      apply (basR D R).repr.injective
      apply DFunLike.coe_injective
      rw [← Algebra.leftMulMatrix_mulVec_repr, hr, Matrix.mulVec_mulVec]
      change Matrix.mulVec (lreg D R a * B) _ = _
      rw [h11, Matrix.one_mulVec]
    have e2 : a' * a = 1 := by
      apply Algebra.leftMulMatrix_injective (basR D R)
      have : lreg D R a * lreg D R a' = 1 := by rw [← map_mul, e1, map_one]
      rw [map_mul, map_one]
      exact mul_eq_one_comm.1 this
    exact ⟨⟨a, a', e1, e2⟩, rfl⟩
  · have := congrFun (congrFun h22 0) 0
    simp only [Matrix.scalar_apply, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul] at this
    exact isUnit_iff_exists_inv.2 ⟨_, by simpa [Matrix.diagonal_mul] using this⟩

variable (σ : D →+* Dᵐᵒᵖ) (β y : D)

theorem tc_one : GlobalTheory.TorCls.TC D σ β y R 1 := by
  refine ⟨?_, Commute.one_left _⟩
  simp

theorem tc_mul (z w : (R ⊗[ℚ] D)ˣ × Rˣ) (hz : GlobalTheory.TorCls.TC D σ β y R z) (hw : GlobalTheory.TorCls.TC D σ β y R w) :
    GlobalTheory.TorCls.TC D σ β y R (z * w) := by
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨hw1, hw2⟩ := hw
  refine ⟨?_, ?_⟩
  · simp only [Prod.fst_mul, Prod.snd_mul, Units.val_mul, map_mul, MulOpposite.unop_mul]
    set B : R ⊗[ℚ] D := (1 : R) ⊗ₜ β
    calc (z.1 : R ⊗[ℚ] D) * w.1 * B * ((starT σ R (w.1 : R ⊗[ℚ] D)).unop * (starT σ R (z.1 : R ⊗[ℚ] D)).unop)
        = z.1 * ((w.1 : R ⊗[ℚ] D) * B * (starT σ R (w.1 : R ⊗[ℚ] D)).unop) * (starT σ R (z.1 : R ⊗[ℚ] D)).unop := by
          simp only [mul_assoc]
      _ = algebraMap R (R ⊗[ℚ] D) (w.2 : R) * ((z.1 : R ⊗[ℚ] D) * B * (starT σ R (z.1 : R ⊗[ℚ] D)).unop) := by
          rw [hw1, ← mul_assoc (z.1 : R ⊗[ℚ] D), ← Algebra.commutes]
          simp only [mul_assoc]
      _ = _ := by
          rw [hz1, ← mul_assoc, ← map_mul, mul_comm (w.2 : R), map_mul]
  · simp only [Prod.fst_mul, Units.val_mul]
    exact hz2.mul_left hw2

theorem tc_inv (z : (R ⊗[ℚ] D)ˣ × Rˣ) (hz : GlobalTheory.TorCls.TC D σ β y R z) :
    GlobalTheory.TorCls.TC D σ β y R z⁻¹ := by
  obtain ⟨hz1, hz2⟩ := hz
  refine ⟨?_, ?_⟩
  · simp only [Prod.fst_inv, Prod.snd_inv]
    set B : R ⊗[ℚ] D := (1 : R) ⊗ₜ β
    set a := z.1
    set c := z.2
    have hs : (starT σ R (a : R ⊗[ℚ] D)).unop * (starT σ R ((a⁻¹ : (R ⊗[ℚ] D)ˣ) : R ⊗[ℚ] D)).unop = 1 := by
      rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
    have e : ((a⁻¹ : (R ⊗[ℚ] D)ˣ) : R ⊗[ℚ] D) * ((a : R ⊗[ℚ] D) * B * (starT σ R (a : R ⊗[ℚ] D)).unop) *
        (starT σ R ((a⁻¹ : (R ⊗[ℚ] D)ˣ) : R ⊗[ℚ] D)).unop = B := by
      rw [show ((a⁻¹ : (R ⊗[ℚ] D)ˣ) : R ⊗[ℚ] D) * ((a : R ⊗[ℚ] D) * B * (starT σ R (a : R ⊗[ℚ] D)).unop) *
          (starT σ R ((a⁻¹ : (R ⊗[ℚ] D)ˣ) : R ⊗[ℚ] D)).unop = (((a⁻¹ : (R ⊗[ℚ] D)ˣ) : R ⊗[ℚ] D) * a) * B *
          ((starT σ R (a : R ⊗[ℚ] D)).unop * (starT σ R ((a⁻¹ : (R ⊗[ℚ] D)ˣ) : R ⊗[ℚ] D)).unop) by
          simp only [mul_assoc], Units.inv_mul, hs, one_mul, mul_one]
    rw [hz1, ← Algebra.smul_def, mul_smul_comm, smul_mul_assoc] at e
    conv_rhs => rw [← e]
    rw [← Algebra.smul_def, smul_smul, Units.inv_mul, one_smul]
  · exact hz2.units_inv_left

end Units
end GlobalTheory.TorLoc

namespace GlobalTheory.TorLoc

section Main

variable (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D)

def Xu : Matrix (Fin (Module.finrank ℚ D + 1)) (Fin (Module.finrank ℚ D + 1))
    (MvPolynomial (Fin (Module.finrank ℚ D + 1) × Fin (Module.finrank ℚ D + 1)) ℚ) :=
  Matrix.of fun i j => MvPolynomial.X (i, j)

def locusSet : Set (MvPolynomial (Fin (Module.finrank ℚ D + 1) × Fin (Module.finrank ℚ D + 1)) ℚ) :=
  Set.range (cond σ β y _ (Xu D))

variable {D}

theorem aeval_cond {R : Type} [CommRing R] [Algebra ℚ R]
    (X : Matrix (Fin (Module.finrank ℚ D + 1)) (Fin (Module.finrank ℚ D + 1)) R) (ω) :
    MvPolynomial.aeval (fun ij : Fin (Module.finrank ℚ D + 1) × Fin (Module.finrank ℚ D + 1) => X ij.1 ij.2)
      (cond σ β y _ (Xu D) ω) = cond σ β y R X ω := by
  rw [cond_map]
  congr 1
  ext i j
  simp [Xu]

theorem mem_zeroLocus_iff {R : Type} [CommRing R] [Algebra ℚ R] (g : GL (Fin (Module.finrank ℚ D + 1)) R) :
    g ∈ HeckeCharacterZeroLocus.zeroLocusGL (locusSet D σ β y) R ↔ ∀ ω, cond σ β y R (g : Matrix _ _ R) ω = 0 := by
  simp only [HeckeCharacterZeroLocus.zeroLocusGL, locusSet, Set.mem_setOf_eq, Set.forall_mem_range, aeval_cond]

variable (D) in

def blkU (R : Type) [CommRing R] [Algebra ℚ R] :
    (R ⊗[ℚ] D)ˣ × Rˣ →* GL (Fin (Module.finrank ℚ D + 1)) R :=
  (Units.map (blk D R).toMonoidHom).comp (MulEquiv.prodUnits.symm.toMonoidHom)

theorem blkU_val {R : Type} [CommRing R] [Algebra ℚ R] (z : (R ⊗[ℚ] D)ˣ × Rˣ) :
    ((blkU D R z : GL (Fin (Module.finrank ℚ D + 1)) R) : Matrix _ _ R) = blk D R ((z.1 : R ⊗[ℚ] D), (z.2 : R)) :=
  rfl

theorem mem_locus_iff {R : Type} [CommRing R] [Algebra ℚ R] (g : GL (Fin (Module.finrank ℚ D + 1)) R) :
    g ∈ HeckeCharacterZeroLocus.zeroLocusGL (locusSet D σ β y) R ↔ ∃ z, GlobalTheory.TorCls.TC D σ β y R z ∧ blkU D R z = g := by
  rw [mem_zeroLocus_iff, cond_zero_iff]
  constructor
  · rintro ⟨hX, hf, hc⟩
    have hmul : blk D R (coordA D R (g : Matrix _ _ R), coordC D R (g : Matrix _ _ R)) *
        ((g⁻¹ : GL (Fin (Module.finrank ℚ D + 1)) R) : Matrix _ _ R) = 1 := by
      rw [← hX, Units.mul_inv]
    obtain ⟨ua, uc⟩ := isUnit_of_blk_mul _ _ hmul
    refine ⟨(ua.unit, uc.unit), ⟨?_, ?_⟩, ?_⟩
    · exact sub_eq_zero.1 hf
    · exact sub_eq_zero.1 hc
    · apply Units.ext
      rw [blkU_val]
      exact hX.symm
  · rintro ⟨z, ⟨h1, h2⟩, rfl⟩
    rw [blkU_val, coordA_blk, coordC_blk]
    exact ⟨rfl, sub_eq_zero.2 h1, sub_eq_zero.2 h2⟩

theorem isGroupLocus : HeckeCharacterZeroLocus.IsGroupLocus (locusSet D σ β y) := by
  intro R _ _
  refine ⟨?_, ?_, ?_⟩
  · exact (mem_locus_iff σ β y _).2 ⟨1, tc_one σ β y, map_one _⟩
  · intro g hg h hh
    obtain ⟨z, hz, rfl⟩ := (mem_locus_iff σ β y _).1 hg
    obtain ⟨w, hw, rfl⟩ := (mem_locus_iff σ β y _).1 hh
    exact (mem_locus_iff σ β y _).2 ⟨z * w, tc_mul σ β y z w hz hw, map_mul _ _ _⟩
  · intro g hg
    obtain ⟨z, hz, rfl⟩ := (mem_locus_iff σ β y _).1 hg
    exact (mem_locus_iff σ β y _).2 ⟨z⁻¹, tc_inv σ β y z hz, map_inv _ _⟩

variable (D) in

def tcSub (R : Type) [CommRing R] [Algebra ℚ R] : Subgroup ((R ⊗[ℚ] D)ˣ × Rˣ) where
  carrier := {z | GlobalTheory.TorCls.TC D σ β y R z}
  mul_mem' {z w} hz hw := tc_mul σ β y z w hz hw
  one_mem' := tc_one σ β y
  inv_mem' {z} hz := tc_inv σ β y z hz

def psi (R : Type) [CommRing R] [Algebra ℚ R] :
    tcSub D σ β y R →* HeckeCharacterZeroLocus.locusSubgroup (locusSet D σ β y) (isGroupLocus σ β y) R :=
  ((blkU D R).comp (tcSub D σ β y R).subtype).codRestrict _
    (fun z => (mem_locus_iff σ β y _).2 ⟨z, z.2, rfl⟩)

theorem psi_bijective (R : Type) [CommRing R] [Algebra ℚ R] : Function.Bijective (psi σ β y R) := by
  constructor
  · intro z w h
    have h' := congrArg (fun g : HeckeCharacterZeroLocus.locusSubgroup (locusSet D σ β y) (isGroupLocus σ β y) R =>
      ((g : GL (Fin (Module.finrank ℚ D + 1)) R) : Matrix (Fin (Module.finrank ℚ D + 1)) (Fin (Module.finrank ℚ D + 1)) R)) h
    have h'' := blk_injective D R h'
    exact Subtype.ext (Prod.ext (Units.ext (congrArg Prod.fst h'')) (Units.ext (congrArg Prod.snd h'')))
  · intro g
    obtain ⟨z, hz, hzg⟩ := (mem_locus_iff σ β y _).1 g.2
    exact ⟨⟨z, hz⟩, Subtype.ext hzg⟩

def phi (R : Type) [CommRing R] [Algebra ℚ R] :
    HeckeCharacterZeroLocus.locusSubgroup (locusSet D σ β y) (isGroupLocus σ β y) R →* (R ⊗[ℚ] D)ˣ × Rˣ :=
  (tcSub D σ β y R).subtype.comp (MulEquiv.ofBijective (psi σ β y R) (psi_bijective σ β y R)).symm.toMonoidHom

theorem blkU_phi (R : Type) [CommRing R] [Algebra ℚ R]
    (g : HeckeCharacterZeroLocus.locusSubgroup (locusSet D σ β y) (isGroupLocus σ β y) R) :
    blkU D R (phi σ β y R g) = g := by
  have := congrArg Subtype.val
    ((MulEquiv.ofBijective (psi σ β y R) (psi_bijective σ β y R)).apply_symm_apply g)
  exact this

theorem phi_fst (R : Type) [CommRing R] [Algebra ℚ R]
    (g : HeckeCharacterZeroLocus.locusSubgroup (locusSet D σ β y) (isGroupLocus σ β y) R) :
    (((phi σ β y R g).1 : (R ⊗[ℚ] D)ˣ) : R ⊗[ℚ] D) =
      coordA D R ((g : GL (Fin (Module.finrank ℚ D + 1)) R) : Matrix (Fin (Module.finrank ℚ D + 1)) (Fin (Module.finrank ℚ D + 1)) R) := by
  rw [← blkU_phi σ β y R g, blkU_val, coordA_blk]

theorem phi_snd (R : Type) [CommRing R] [Algebra ℚ R]
    (g : HeckeCharacterZeroLocus.locusSubgroup (locusSet D σ β y) (isGroupLocus σ β y) R) :
    (((phi σ β y R g).2 : Rˣ) : R) =
      coordC D R ((g : GL (Fin (Module.finrank ℚ D + 1)) R) : Matrix (Fin (Module.finrank ℚ D + 1)) (Fin (Module.finrank ℚ D + 1)) R) := by
  rw [← blkU_phi σ β y R g, blkU_val, coordC_blk]

end Main
end GlobalTheory.TorLoc

namespace GlobalTheory.TorLoc

section Final

variable {D : Type} [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D)

theorem coordA_eq_sum {R : Type} [CommRing R] [Algebra ℚ R]
    (X : Matrix (Fin (Module.finrank ℚ D + 1)) (Fin (Module.finrank ℚ D + 1)) R) :
    coordA D R X = ∑ i, (∑ j, X (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) *
      (basR D R).repr 1 j) • basR D R i := by
  simp only [coordA, Module.Basis.equivFun_symm_apply]

theorem continuous_coordA {R : Type} [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R]
    [TopologicalSpace (R ⊗[ℚ] D)] [IsModuleTopology R (R ⊗[ℚ] D)] : Continuous (coordA D R) := by
  haveI : ContinuousAdd (R ⊗[ℚ] D) := IsModuleTopology.toContinuousAdd R _
  have : coordA D R = fun X => ∑ i, (∑ j, X (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) *
      (basR D R).repr 1 j) • basR D R i := funext coordA_eq_sum
  rw [this]
  refine continuous_finset_sum _ fun i _ => ?_
  refine Continuous.smul (f := fun X : Matrix (Fin (Module.finrank ℚ D + 1)) (Fin (Module.finrank ℚ D + 1)) R =>
      ∑ j, X (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) * (basR D R).repr 1 j)
    (g := fun _ => basR D R i) (continuous_finset_sum _ fun j _ => ?_) continuous_const
  exact (continuous_apply_apply _ _).mul continuous_const

theorem continuous_coordC {R : Type} [CommRing R] [Algebra ℚ R] [TopologicalSpace R] :
    Continuous (coordC D R) := continuous_apply_apply _ _

theorem continuous_phi (R : Type) [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R]
    [TopologicalSpace (R ⊗[ℚ] D)] [IsModuleTopology R (R ⊗[ℚ] D)] : Continuous (phi σ β y R) := by
  have hv : Continuous fun g : HeckeCharacterZeroLocus.locusSubgroup (locusSet D σ β y) (isGroupLocus σ β y) R =>
      ((g : GL (Fin (Module.finrank ℚ D + 1)) R) :
        Matrix (Fin (Module.finrank ℚ D + 1)) (Fin (Module.finrank ℚ D + 1)) R) :=
    Units.continuous_val.comp continuous_subtype_val
  have hi : Continuous fun g : HeckeCharacterZeroLocus.locusSubgroup (locusSet D σ β y) (isGroupLocus σ β y) R =>
      (((g⁻¹ : HeckeCharacterZeroLocus.locusSubgroup (locusSet D σ β y) (isGroupLocus σ β y) R) :
        GL (Fin (Module.finrank ℚ D + 1)) R) :
        Matrix (Fin (Module.finrank ℚ D + 1)) (Fin (Module.finrank ℚ D + 1)) R) :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  refine Continuous.prodMk (f := fun g => (phi σ β y R g).1) (g := fun g => (phi σ β y R g).2) ?_ ?_
  · refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (continuous_coordA.comp hv).congr fun g => (phi_fst σ β y R g).symm
    · refine (continuous_coordA.comp hi).congr fun g => ?_
      have := phi_fst σ β y R g⁻¹
      rw [map_inv] at this
      exact this.symm
  · refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (continuous_coordC.comp hv).congr fun g => (phi_snd σ β y R g).symm
    · refine (continuous_coordC.comp hi).congr fun g => ?_
      have := phi_snd σ β y R g⁻¹
      rw [map_inv] at this
      exact this.symm

end Final

theorem exists_locus :
    ∀ (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D),
  ∃ (N : ℕ) (S : Set (MvPolynomial (Fin N × Fin N) ℚ)) (hS : HeckeCharacterZeroLocus.IsGroupLocus S)
    (φ : ∀ (R : Type) [CommRing R] [Algebra ℚ R], HeckeCharacterZeroLocus.locusSubgroup S hS R →* (R ⊗[ℚ] D)ˣ × Rˣ),
    (∀ (R : Type) [CommRing R] [Algebra ℚ R], Function.Injective (φ R) ∧
      ∀ z : (R ⊗[ℚ] D)ˣ × Rˣ, GlobalTheory.TorCls.TC D σ β y R z ↔ z ∈ Set.range (φ R)) ∧
    (∀ (R R' : Type) [CommRing R] [Algebra ℚ R] [CommRing R'] [Algebra ℚ R'] (f : R →ₐ[ℚ] R')
      (g : HeckeCharacterZeroLocus.locusSubgroup S hS R) (g' : HeckeCharacterZeroLocus.locusSubgroup S hS R'),
      (g' : GL (Fin N) R') = Units.map (f.toRingHom.mapMatrix : Matrix (Fin N) (Fin N) R →+* Matrix (Fin N) (Fin N) R').toMonoidHom (g : GL (Fin N) R) →
      φ R' g' = (Units.map (Algebra.TensorProduct.map f (AlgHom.id ℚ D)).toRingHom.toMonoidHom (φ R g).1,
        Units.map f.toRingHom.toMonoidHom (φ R g).2)) ∧
    (∀ (R : Type) [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R],
      letI : TopologicalSpace (R ⊗[ℚ] D) := moduleTopology R (R ⊗[ℚ] D)
      Continuous (φ R)) := by
  intro D _ _ _ σ β y
  refine ⟨Module.finrank ℚ D + 1, locusSet D σ β y, isGroupLocus σ β y, fun R _ _ => phi σ β y R, ?_, ?_, ?_⟩
  · intro R _ _
    refine ⟨?_, fun z => ⟨fun hz => ?_, ?_⟩⟩
    · intro g h hgh
      apply Subtype.ext
      rw [← blkU_phi σ β y R g, ← blkU_phi σ β y R h]
      exact congrArg _ hgh
    · refine ⟨psi σ β y R ⟨z, hz⟩, ?_⟩
      exact congrArg Subtype.val
        ((MulEquiv.ofBijective (psi σ β y R) (psi_bijective σ β y R)).symm_apply_apply ⟨z, hz⟩)
    · rintro ⟨g, rfl⟩
      exact ((MulEquiv.ofBijective (psi σ β y R) (psi_bijective σ β y R)).symm g).2
  · intro R R' _ _ _ _ f g g' hg
    refine Prod.ext (Units.ext ?_) (Units.ext ?_)
    · have h1 := phi_fst σ β y R' g'
      rw [hg] at h1
      refine h1.trans ((coordA_map f _).trans ?_)
      exact congrArg _ (phi_fst σ β y R g).symm
    · have h1 := phi_snd σ β y R' g'
      rw [hg] at h1
      refine h1.trans ((coordC_map f _).trans ?_)
      exact congrArg _ (phi_snd σ β y R g).symm
  · intro R _ _ _ _
    letI : TopologicalSpace (R ⊗[ℚ] D) := moduleTopology R (R ⊗[ℚ] D)
    haveI : IsModuleTopology R (R ⊗[ℚ] D) := ⟨rfl⟩
    exact continuous_phi σ β y R

end GlobalTheory.TorLoc
