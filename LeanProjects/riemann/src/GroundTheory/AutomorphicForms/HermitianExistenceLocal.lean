import Mathlib
import GroundTheory.AutomorphicForms.HermitianHasse
import GroundTheory.AutomorphicForms.HermitianClassification

noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix

section Transport

variable {A B : Type*} [CommRing A] [CommRing B] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem det_map_ringEquiv (e : A ≃+* B) (H : Matrix ι ι A) : (H.map e).det = e H.det :=
  ((e : A →+* B).map_det H).symm

theorem isCongr_map_iff (e : A ≃+* B) {s : A →+* A} {t : B →+* B} (he : ∀ x, e (s x) = t (e x))
    {H H' : Matrix ι ι A} : IsCongr t (H.map e) (H'.map e) ↔ IsCongr s H H' := by
  refine ⟨fun h => ?_, fun h => h.map (e : A →+* B) he⟩
  have he' : ∀ y, e.symm (t y) = s (e.symm y) := fun y => by
    apply e.injective
    rw [e.apply_symm_apply, he, e.apply_symm_apply]
  have hid : ∀ M : Matrix ι ι A, (M.map e).map (e.symm : B →+* A) = M := fun M => by
    ext i j
    simp
  have := h.map (e.symm : B →+* A) he'
  rwa [hid, hid] at this

omit [Fintype ι] [DecidableEq ι] in

theorem IsHermitianFor.map {s : A →+* A} {t : B →+* B} (φ : A →+* B) (hφ : ∀ x, φ (s x) = t (φ x))
    {H : Matrix ι ι A} (hH : IsHermitianFor s H) : IsHermitianFor t (H.map φ) := by
  unfold IsHermitianFor at *
  conv_rhs => rw [← hH]
  ext i j
  simp [hφ]

end Transport

section Split

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem isCongr_one_of_split (H : Matrix ι ι (F × F)) (hH : IsHermitianFor (conjHom F (F × F)) H)
    (hu : IsUnit H.det) : IsCongr (conjHom F (F × F)) H 1 := by
  set A := H.map (RingHom.fst F F) with hA_def
  have hA : IsUnit A.det := by
    rw [hA_def, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hu.map _
  have hHsnd : H.map (RingHom.snd F F) = Aᵀ := by
    conv_lhs => rw [← hH]
    rw [transpose_map, map_snd_map_conjHom_prod]
  set P : Matrix ι ι (F × F) := fun i j => (A⁻¹ i j, (1 : Matrix ι ι F) i j) with hP_def
  have hPfst : P.map (RingHom.fst F F) = A⁻¹ := by ext i j; rfl
  have hPsnd : P.map (RingHom.snd F F) = 1 := by ext i j; rfl
  have hP : IsUnit P.det := by
    rw [Prod.isUnit_iff]
    constructor
    · change IsUnit ((RingHom.fst F F) P.det)
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hPfst]
      exact (Matrix.isUnit_nonsing_inv_det_iff.2 hA)
    · change IsUnit ((RingHom.snd F F) P.det)
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hPsnd, det_one]
      exact isUnit_one
  refine ⟨P, hP, ?_⟩
  have h1 : ((P.map (conjHom F (F × F)))ᵀ * H * P).map (RingHom.fst F F) =
      (1 : Matrix ι ι (F × F)).map (RingHom.fst F F) := by
    rw [Matrix.map_mul, Matrix.map_mul, transpose_map, map_fst_map_conjHom_prod, hPsnd, hPfst,
      Matrix.map_one _ (map_zero _) (map_one _), transpose_one, Matrix.one_mul,
      Matrix.mul_nonsing_inv _ hA]
  have h2 : ((P.map (conjHom F (F × F)))ᵀ * H * P).map (RingHom.snd F F) =
      (1 : Matrix ι ι (F × F)).map (RingHom.snd F F) := by
    rw [Matrix.map_mul, Matrix.map_mul, transpose_map, map_snd_map_conjHom_prod, hPsnd, hPfst,
      hHsnd, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, ← transpose_mul,
      Matrix.mul_nonsing_inv _ hA, transpose_one]
  funext i j
  exact Prod.ext (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)

def sqSplitEquiv (h2 : (2 : F) ≠ 0) {d r : F} (hr : r ≠ 0) (hd : r ^ 2 = d) :
    QuadraticAlgebra F d 0 ≃+* F × F where
  toFun z := (z.re + r * z.im, z.re - r * z.im)
  invFun p := ⟨(p.1 + p.2) / 2, (p.1 - p.2) / (2 * r)⟩
  left_inv z := by
    ext <;> simp <;> field_simp <;> ring
  right_inv p := by
    ext <;> simp <;> field_simp <;> ring
  map_mul' z w := by
    subst hd
    ext <;> simp <;> ring
  map_add' z w := by
    ext <;> simp <;> ring

theorem sqSplitEquiv_star (h2 : (2 : F) ≠ 0) {d r : F} (hr : r ≠ 0) (hd : r ^ 2 = d)
    (z : QuadraticAlgebra F d 0) :
    sqSplitEquiv h2 hr hd (conjHom F (QuadraticAlgebra F d 0) z) =
      conjHom F (F × F) (sqSplitEquiv h2 hr hd z) := by
  change sqSplitEquiv h2 hr hd (conj F (QuadraticAlgebra F d 0) z) =
    conj F (F × F) (sqSplitEquiv h2 hr hd z)
  rw [conj_quadraticAlgebra, conj_prod]
  ext
  · simp [sqSplitEquiv, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
    ring
  · simp [sqSplitEquiv, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]

theorem isCongr_of_eq_sq (h2 : (2 : F) ≠ 0) {d r : F} (hr : r ≠ 0) (hd : r ^ 2 = d)
    {H H' : Matrix ι ι (QuadraticAlgebra F d 0)}
    (hH : IsHermitianFor (conjHom F (QuadraticAlgebra F d 0)) H)
    (hH' : IsHermitianFor (conjHom F (QuadraticAlgebra F d 0)) H')
    (hu : IsUnit H.det) (hu' : IsUnit H'.det) :
    IsCongr (conjHom F (QuadraticAlgebra F d 0)) H H' := by
  set e := sqSplitEquiv h2 hr hd
  have he := sqSplitEquiv_star h2 hr hd
  rw [← isCongr_map_iff e he]
  have k1 := isCongr_one_of_split (H.map e) (hH.map (e : _ →+* F × F) he)
    (by rw [det_map_ringEquiv]; exact hu.map e)
  have k2 := isCongr_one_of_split (H'.map e) (hH'.map (e : _ →+* F × F) he)
    (by rw [det_map_ringEquiv]; exact hu'.map e)
  exact k1.trans k2.symm

end Split

section OfGram

variable {F A : Type*} [Field F] [Field A] [Algebra F A] [Algebra.IsQuadraticExtension F A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def HermitianForm.ofGram (H : Matrix ι ι A) (hH : IsHermitianFor (conjHom F A) H)
    (hu : IsUnit H.det) : HermitianForm F A (ι → A) where
  toSesq := LinearMap.mk₂'ₛₗ (conjHom F A) (RingHom.id A)
    (fun x y => ∑ i, ∑ j, conj F A (x i) * H i j * y j)
    (fun x x' y => by
      simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, conjHom_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
    (fun x y y' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
  isSymm := ⟨fun x y => by
    simp only [LinearMap.mk₂'ₛₗ_apply, conjHom_apply, map_sum, map_mul, conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : conj F A (H j i) = H i j := congrFun (congrFun hH i) j
    rw [this]
    ring⟩
  nonsingular := by
    refine bijective_of_injective_sesq _ ?_
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hv : Matrix.vecMul (fun i => conj F A (x i)) H = 0 := by
      funext j
      have := LinearMap.congr_fun hx (Pi.single j 1)
      rw [LinearMap.mk₂'ₛₗ_apply] at this
      simpa [vecMul, dotProduct, Pi.single_apply] using this
    have hinj := (Matrix.vecMul_injective_iff_isUnit (A := H)).2
      ((Matrix.isUnit_iff_isUnit_det H).2 hu)
    have h0 := hinj (hv.trans (Matrix.zero_vecMul H).symm)
    funext i
    have := congrFun h0 i
    rw [← conj_conj (F := F) (x i), this]
    simp

theorem HermitianForm.ofGram_apply (H : Matrix ι ι A) (hH : IsHermitianFor (conjHom F A) H)
    (hu : IsUnit H.det) (x y : ι → A) :
    (HermitianForm.ofGram H hH hu).toSesq x y = ∑ i, ∑ j, conj F A (x i) * H i j * y j :=
  rfl

theorem gram_ofGram (H : Matrix ι ι A) (hH : IsHermitianFor (conjHom F A) H)
    (hu : IsUnit H.det) :
    gram (HermitianForm.ofGram H hH hu).toSesq (Pi.basisFun A ι) = H := by
  ext i j
  rw [gram_apply, HermitianForm.ofGram_apply]
  simp [Pi.single_apply]

theorem isCongr_ofGram_iff (H H' : Matrix ι ι A) (hH : IsHermitianFor (conjHom F A) H)
    (hu : IsUnit H.det) (hH' : IsHermitianFor (conjHom F A) H') (hu' : IsUnit H'.det) :
    HermitianForm.Isometric (HermitianForm.ofGram H hH hu) (HermitianForm.ofGram H' hH' hu') ↔
      IsCongr (conjHom F A) H H' := by
  rw [isometric_iff_isCongr, gram_ofGram, gram_ofGram]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

end OfGram

section LocalField

variable {F A : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field A] [Algebra F A] [Algebra.IsQuadraticExtension F A] [Algebra.IsSeparable F A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem isCongr_of_det_eq_mul_norm {H H' : Matrix ι ι A} (hH : IsHermitianFor (conjHom F A) H)
    (hu : IsUnit H.det) (hH' : IsHermitianFor (conjHom F A) H') (hu' : IsUnit H'.det) {z : A}
    (hz : H'.det = H.det * (conj F A z * z)) : IsCongr (conjHom F A) H H' := by
  set h := HermitianForm.ofGram H hH hu
  set h' := HermitianForm.ofGram H' hH' hu'
  have hd : h.disc = h'.disc := by
    rw [h.disc_eq (Pi.basisFun A ι), h'.disc_eq (Pi.basisFun A ι), QuotientGroup.eq,
      mem_range_normUnits_iff]
    refine ⟨z, ?_⟩
    apply (algebraMap F A).injective
    rw [← mul_conj, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀,
      HermitianForm.algebraMap_detUnit, HermitianForm.algebraMap_detUnit, gram_ofGram,
      gram_ofGram, hz]
    have := hu.ne_zero
    field_simp
  have hI := (HermitianForm.isometric_iff h h').2 ⟨rfl, hd⟩
  exact (isCongr_ofGram_iff H H' hH hu hH' hu').1 hI

end LocalField

section Diagonal

variable {F A : Type*} [Field F] [Field A] [Algebra F A] [Algebra.IsQuadraticExtension F A]

theorem exists_isCongr_diagonal [Algebra.IsSeparable F A] {n : ℕ}
    (H : Matrix (Fin n) (Fin n) A) (hH : IsHermitianFor (conjHom F A) H) (hu : IsUnit H.det) :
    ∃ c : Fin n → Fˣ, IsCongr (conjHom F A) (diagonal fun i => algebraMap F A (c i)) H := by
  obtain ⟨c, hc⟩ := exists_isometric_diagForm n (HermitianForm.ofGram H hH hu) (by simp)
  refine ⟨c, ?_⟩
  have := (isometric_iff_isCongr _ _).1 hc
  rwa [gram_diagForm, gram_ofGram] at this

theorem isCongr_diagonal_of_sq {ι : Type*} [Fintype ι] [DecidableEq ι] (a c s : ι → F)
    (hs0 : ∀ i, s i ≠ 0) (hs : ∀ i, s i ^ 2 * a i = c i) :
    IsCongr (conjHom F A) (diagonal fun i => algebraMap F A (a i))
      (diagonal fun i => algebraMap F A (c i)) := by
  refine ⟨diagonal fun i => algebraMap F A (s i), ?_, ?_⟩
  · rw [det_diagonal]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => (map_ne_zero _).2 (hs0 i))
  · rw [diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal,
      diagonal_mul_diagonal]
    congr 1
    funext i
    rw [conjHom_apply, conj_algebraMap, ← hs i]
    simp only [map_mul, map_pow]
    ring

end Diagonal

end GroundTheory.Automorphic
