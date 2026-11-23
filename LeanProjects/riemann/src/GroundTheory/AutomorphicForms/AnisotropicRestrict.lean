import Mathlib
set_option maxSynthPendingDepth 1

open Matrix TensorProduct

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

noncomputable section

namespace Anisotropic

variable {K : Type*} [Field K] {κ : Type*} [Fintype κ] [DecidableEq κ]

section General

variable {A : Type*} [Ring A] [Algebra K A] (b : Module.Basis κ K A)
variable (R : Type*) [CommRing R] [Algebra K R]

abbrev baseBasis : Module.Basis κ R (R ⊗[K] A) := Algebra.TensorProduct.basis R b

def coords : (R ⊗[K] A) ≃ₗ[R] (κ → R) := (baseBasis b R).equivFun

theorem baseBasis_apply (k : κ) : baseBasis b R k = 1 ⊗ₜ b k :=
  Algebra.TensorProduct.basis_apply b k

theorem coords_baseBasis (k : κ) : coords b R (baseBasis b R k) = Pi.single k 1 := by
  funext l
  rw [coords, Module.Basis.equivFun_self, Pi.single_apply]
  exact if_congr eq_comm rfl rfl

theorem eq_sum_coords (z : R ⊗[K] A) : z = ∑ k, coords b R z k • baseBasis b R k :=
  ((baseBasis b R).sum_equivFun z).symm

def rmat (x : R ⊗[K] A) : Matrix κ κ R := fun k => coords b R (baseBasis b R k * x)

def lmat (a : R ⊗[K] A) : Matrix κ κ R := fun k => coords b R (a * baseBasis b R k)

theorem coords_mul (z x : R ⊗[K] A) : coords b R (z * x) = coords b R z ᵥ* rmat b R x := by
  conv_lhs => rw [eq_sum_coords b R z]
  rw [Finset.sum_mul, map_sum]
  funext l
  simp only [smul_mul_assoc, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vecMul,
    dotProduct, rmat]

theorem coords_mul_left (a z : R ⊗[K] A) : coords b R (a * z) = coords b R z ᵥ* lmat b R a := by
  conv_lhs => rw [eq_sum_coords b R z]
  rw [Finset.mul_sum, map_sum]
  funext l
  simp only [mul_smul_comm, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vecMul,
    dotProduct, lmat]

theorem rmat_mul (x y : R ⊗[K] A) : rmat b R (x * y) = rmat b R x * rmat b R y := by
  ext k l
  simp only [rmat]
  rw [← mul_assoc, coords_mul]
  simp only [vecMul, dotProduct, Matrix.mul_apply, rmat]

theorem rmat_one : rmat b R 1 = 1 := by
  ext k l
  simp only [rmat, mul_one, coords_baseBasis, Pi.single_apply, Matrix.one_apply, eq_comm]

def rmatHom : R ⊗[K] A →ₐ[R] Matrix κ κ R :=
  AlgHom.ofLinearMap
    { toFun := rmat b R
      map_add' := fun x y => by
        ext k l
        simp [rmat, mul_add]
      map_smul' := fun c x => by
        ext k l
        simp [rmat] }
    (rmat_one b R) (rmat_mul b R)

@[simp]
theorem rmatHom_apply (x : R ⊗[K] A) : rmatHom b R x = rmat b R x := rfl

theorem rmat_injective : Function.Injective (rmat b R) := by
  intro x y h
  have hx := coords_mul b R 1 x
  have hy := coords_mul b R 1 y
  rw [one_mul] at hx hy
  rw [h] at hx
  exact (coords b R).injective (hx.trans hy.symm)

theorem exists_rmat_eq (g : Matrix κ κ R)
    (hg : ∀ j, lmat b R (baseBasis b R j) * g = g * lmat b R (baseBasis b R j)) :
    ∃ x, rmat b R x = g := by
  let φ : R ⊗[K] A →ₗ[R] R ⊗[K] A :=
    (coords b R).symm.toLinearMap ∘ₗ g.vecMulLinear ∘ₗ (coords b R).toLinearMap
  have hφ : ∀ z, coords b R (φ z) = coords b R z ᵥ* g := by
    intro z
    simp [φ]
  have hj : ∀ j z, φ (baseBasis b R j * z) = baseBasis b R j * φ z := by
    intro j z
    apply (coords b R).injective
    rw [hφ, coords_mul_left, coords_mul_left, hφ, vecMul_vecMul, vecMul_vecMul, hg]
  have ha : ∀ a z, φ (a * z) = a * φ z := by
    intro a z
    rw [eq_sum_coords b R a, Finset.sum_mul, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc, map_smul, hj]
  refine ⟨φ 1, ?_⟩
  ext k l
  have h1 : baseBasis b R k * φ 1 = φ (baseBasis b R k) := by rw [← ha, mul_one]
  simp only [rmat, h1, hφ, coords_baseBasis, single_one_vecMul, Matrix.row_apply]

variable {R} {R' : Type*} [CommRing R'] [Algebra K R']

def baseMap (f : R →ₐ[K] R') : R ⊗[K] A →ₐ[K] R' ⊗[K] A :=
  Algebra.TensorProduct.map f (AlgHom.id K A)

theorem baseMap_baseBasis (f : R →ₐ[K] R') (k : κ) :
    baseMap f (baseBasis b R k) = baseBasis b R' k := by
  rw [baseBasis_apply, baseBasis_apply, baseMap, Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem coords_baseMap (f : R →ₐ[K] R') (z : R ⊗[K] A) :
    coords b R' (baseMap f z) = f ∘ coords b R z := by
  have h : ∀ k, baseMap f (coords b R z k • baseBasis b R k) =
      f (coords b R z k) • baseBasis b R' k := by
    intro k
    simp only [baseBasis_apply, baseMap, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
  conv_lhs => rw [eq_sum_coords b R z]
  rw [map_sum, Finset.sum_congr rfl fun k _ => h k, map_sum]
  funext l
  rw [Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, coords_baseBasis, smul_eq_mul, Pi.single_apply, mul_ite,
    mul_one, mul_zero, Function.comp_apply]
  rw [Finset.sum_ite_eq]
  simp

theorem rmat_baseMap (f : R →ₐ[K] R') (x : R ⊗[K] A) :
    rmat b R' (baseMap f x) = (rmat b R x).map f := by
  ext k l
  simp only [rmat, Matrix.map_apply, ← baseMap_baseBasis b f k, ← map_mul, coords_baseMap,
    Function.comp_apply]

end General

section Block

variable {E : Type*} [CommRing E] [Algebra K E] (b : Module.Basis κ K E)
variable (R : Type*) [CommRing R] [Algebra K R] {R' : Type*} [CommRing R'] [Algebra K R']
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem lmat_eq_rmat (a : R ⊗[K] E) : lmat b R a = rmat b R a := by
  ext k l
  simp only [lmat, rmat, mul_comm]

def blockHom : Matrix ι ι (R ⊗[K] E) →ₐ[R] Matrix (ι × κ) (ι × κ) R :=
  (Matrix.compAlgEquiv ι κ R R).toAlgHom.comp (rmatHom b R).mapMatrix

theorem blockHom_apply (M : Matrix ι ι (R ⊗[K] E)) (i j : ι) (k l : κ) :
    blockHom b R M (i, k) (j, l) = rmat b R (M i j) k l := rfl

theorem blockHom_injective : Function.Injective (blockHom (ι := ι) b R) := by
  intro M M' h
  ext i j : 2
  apply rmat_injective b R
  ext k l
  exact congrFun (congrFun h (i, k)) (j, l)

def coordsVec (x : ι → R ⊗[K] E) : ι × κ → R := fun p => coords b R (x p.1) p.2

theorem coordsVec_vecMul (x : ι → R ⊗[K] E) (M : Matrix ι ι (R ⊗[K] E)) :
    coordsVec b R (x ᵥ* M) = coordsVec b R x ᵥ* blockHom b R M := by
  funext ⟨j, l⟩
  simp only [coordsVec, vecMul, dotProduct, map_sum, Finset.sum_apply, coords_mul,
    Fintype.sum_prod_type, blockHom_apply]

theorem exists_blockHom_eq (g : Matrix (ι × κ) (ι × κ) R)
    (hg : ∀ j, blockHom b R (Matrix.scalar ι (baseBasis b R j)) * g =
      g * blockHom b R (Matrix.scalar ι (baseBasis b R j))) :
    ∃ M, blockHom b R M = g := by
  have hsc : ∀ j, blockHom b R (Matrix.scalar ι (baseBasis b R j)) =
      Matrix.compAlgEquiv ι κ R R (Matrix.scalar ι (rmat b R (baseBasis b R j))) := by
    intro j
    simp only [blockHom, AlgHom.comp_apply, AlgHom.mapMatrix_apply, Matrix.scalar_apply,
      Matrix.diagonal_map (map_zero _), rmatHom_apply]
    rfl
  have hcomm : ∀ j i i', rmat b R (baseBasis b R j) * (Matrix.comp ι ι κ κ R).symm g i i' =
      (Matrix.comp ι ι κ κ R).symm g i i' * rmat b R (baseBasis b R j) := by
    intro j i i'
    have h := hg j
    rw [hsc, ← (Matrix.compAlgEquiv ι κ R R).apply_symm_apply g, ← map_mul, ← map_mul] at h
    have h2 := (Matrix.compAlgEquiv ι κ R R).injective h
    have h3 := congrFun (congrFun h2 i) i'
    simpa [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal] using h3
  have hx : ∀ i i', ∃ x, rmat b R x = (Matrix.comp ι ι κ κ R).symm g i i' := fun i i' =>
    exists_rmat_eq b R _ fun j => by rw [lmat_eq_rmat]; exact hcomm j i i'
  choose M hM using hx
  refine ⟨Matrix.of M, ?_⟩
  ext ⟨i, k⟩ ⟨i', l⟩
  rw [blockHom_apply, Matrix.of_apply, hM i i']
  rfl

variable {R}

theorem blockHom_baseMap (f : R →ₐ[K] R') (M : Matrix ι ι (R ⊗[K] E)) :
    blockHom b R' (M.map (baseMap f)) = (blockHom b R M).map f := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [blockHom_apply, Matrix.map_apply, rmat_baseMap]

theorem coordsVec_baseMap (f : R →ₐ[K] R') (x : ι → R ⊗[K] E) :
    coordsVec b R' (fun i => baseMap f (x i)) = f ∘ coordsVec b R x := by
  funext ⟨i, k⟩
  simp only [coordsVec, coords_baseMap, Function.comp_apply]

end Block

end Anisotropic

end

end GroundTheory.Automorphic
