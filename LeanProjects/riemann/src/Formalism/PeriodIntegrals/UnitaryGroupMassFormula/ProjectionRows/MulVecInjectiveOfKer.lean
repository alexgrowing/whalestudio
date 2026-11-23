import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionRows.Pieces

noncomputable section

namespace PI.DvRows

namespace GramDeterminantPositive

open Matrix
open scoped ComplexOrder

section Mat

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma psd_det_real {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    A.det = ((A.det.re : ℝ) : ℂ) ∧ 0 ≤ A.det.re := by
  have h := hA.det_nonneg
  rw [Complex.nonneg_iff] at h
  exact ⟨Complex.ext (by simp) (by simp [← h.2]), h.1⟩

lemma pd_det_real {A : Matrix n n ℂ} (hA : A.PosDef) :
    A.det = ((A.det.re : ℝ) : ℂ) ∧ 0 < A.det.re := by
  have h := hA.det_pos
  rw [Complex.lt_def] at h
  refine ⟨Complex.ext (by simp) (by simp [← h.2]), by simpa using h.1⟩

lemma det_one_add_psd {N : Matrix n n ℂ} (hN : N.PosSemidef) :
    ∃ t : ℝ, 1 ≤ t ∧ (1 + N).det = (t : ℂ) := by
  have hH := hN.isHermitian
  have hs := hH.spectral_theorem
  set U := hH.eigenvectorUnitary with hUdef
  have hU : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 :=
    Unitary.mul_star_self_of_mem U.2
  have key : 1 + N = (U : Matrix n n ℂ) * (1 + diagonal (RCLike.ofReal ∘ hH.eigenvalues)) *
      star (U : Matrix n n ℂ) := by
    conv_lhs => rw [hs]
    rw [Unitary.conjStarAlgAut_apply, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hU]
  have hdU : (U : Matrix n n ℂ).det * (star (U : Matrix n n ℂ)).det = 1 := by
    rw [← det_mul, hU, det_one]
  refine ⟨∏ i, (1 + hH.eigenvalues i), ?_, ?_⟩
  · calc (1 : ℝ) = ∏ _i : n, (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one)
          (fun i _ => by linarith [hN.eigenvalues_nonneg i])
  · rw [key, det_mul, det_mul]
    have h1 : (1 + diagonal (RCLike.ofReal ∘ hH.eigenvalues) : Matrix n n ℂ) =
        diagonal (fun i => ((1 + hH.eigenvalues i : ℝ) : ℂ)) := by
      rw [← diagonal_one, diagonal_add]; congr 1; funext i; simp
    rw [h1, det_diagonal]
    calc (U : Matrix n n ℂ).det * (∏ i, ((1 + hH.eigenvalues i : ℝ) : ℂ)) *
          (star (U : Matrix n n ℂ)).det
        = (∏ i, ((1 + hH.eigenvalues i : ℝ) : ℂ)) * ((U : Matrix n n ℂ).det *
          (star (U : Matrix n n ℂ)).det) := by ring
      _ = _ := by rw [hdU, mul_one]; push_cast; rfl

lemma mulVec_injective_of_ker {m k : Type*} [Fintype k] {P : Matrix m k ℂ}
    (h : ∀ v, P *ᵥ v = 0 → v = 0) : Function.Injective P.mulVec := fun a b hab =>
  sub_eq_zero.1 (h _ (by rw [mulVec_sub, hab, sub_self]))

variable {m : Type*} [Fintype m] [DecidableEq m]

theorem gram_cs {k : Type*} [Fintype k] [DecidableEq k] (P Q : Matrix m k ℂ) :
    ‖(Pᴴ * Q).det‖ ^ 2 ≤ (Pᴴ * P).det.re * (Qᴴ * Q).det.re := by
  have hP := posSemidef_conjTranspose_mul_self P
  have hQ := posSemidef_conjTranspose_mul_self Q
  obtain ⟨_, hP0⟩ := psd_det_real hP
  obtain ⟨_, hQ0⟩ := psd_det_real hQ
  by_cases hB : (Pᴴ * Q).det = 0
  · rw [hB, norm_zero]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact mul_nonneg hP0 hQ0
  have hPinj : Function.Injective P.mulVec := mulVec_injective_of_ker fun v hv => by
    by_contra hne
    apply hB
    have h1 : (Pᴴ * Q)ᴴ *ᵥ v = 0 := by
      rw [conjTranspose_mul, conjTranspose_conjTranspose, ← mulVec_mulVec, hv, mulVec_zero]
    have h0 : (Pᴴ * Q)ᴴ.det = 0 := (exists_mulVec_eq_zero_iff).1 ⟨v, hne, h1⟩
    rwa [det_conjTranspose, star_eq_zero] at h0
  set A := Pᴴ * P with hAdef
  set B := Pᴴ * Q with hBdef
  set D := Qᴴ * Q with hDdef
  have hApd : A.PosDef := PosDef.conjTranspose_mul_self P hPinj
  obtain ⟨hAr, hA0⟩ := pd_det_real hApd
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.2 (by
    intro h0; rw [h0] at hA0; simp at hA0)
  have hBinj : Function.Injective B.mulVec :=
    (mulVec_injective_iff_isUnit).2 ((isUnit_iff_isUnit_det B).2 (isUnit_iff_ne_zero.2 hB))
  set X := A⁻¹ * B with hXdef
  have hAX : A * X = B := by
    rw [hXdef, ← Matrix.mul_assoc, mul_nonsing_inv _ hAu, Matrix.one_mul]
  set R := Q - P * X with hRdef
  have hRR : Rᴴ * R = D - Bᴴ * X := by
    have e1 : Qᴴ * (P * X) = Bᴴ * X := by
      rw [hBdef, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    have e2 : Xᴴ * Pᴴ * Q = Xᴴ * B := by rw [hBdef, Matrix.mul_assoc]
    have e3 : Xᴴ * Pᴴ * (P * X) = Xᴴ * B := by
      rw [← hAX, hAdef, Matrix.mul_assoc, Matrix.mul_assoc]
    rw [hRdef, conjTranspose_sub, conjTranspose_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      e1, e2, e3, hDdef]
    abel
  set C := Bᴴ * X with hCdef
  have hCpd : C.PosDef := by
    have := (hApd.inv).conjTranspose_mul_mul_same hBinj
    rwa [Matrix.mul_assoc] at this
  have hCu : IsUnit C.det := isUnit_iff_ne_zero.2 (hCpd.det_pos.ne')
  have hD : D = C * (1 + (C⁻¹ * Rᴴ) * R) := by
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hCu,
      Matrix.one_mul, hRR]
    abel
  have hN : (R * (C⁻¹ * Rᴴ)).PosSemidef := by
    have := hCpd.inv.posSemidef.mul_mul_conjTranspose_same R
    rwa [Matrix.mul_assoc] at this
  obtain ⟨t, ht1, ht⟩ := det_one_add_psd hN
  set a := A.det.re with ha
  have hbb : star B.det * B.det = ((‖B.det‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
  have hdetC : C.det = star B.det * B.det / (a : ℂ) := by
    rw [hCdef, hXdef, det_mul, det_mul, det_conjTranspose, det_nonsing_inv, Ring.inverse_eq_inv', hAr]
    ring
  have hdetD : D.det = ((‖B.det‖ ^ 2 / a * t : ℝ) : ℂ) := by
    rw [hD, det_mul, det_one_add_mul_comm, ht, hdetC, hbb]
    push_cast; ring
  rw [hdetD, Complex.ofReal_re]
  have hb0 : 0 ≤ ‖B.det‖ ^ 2 := sq_nonneg _
  have : a * (‖B.det‖ ^ 2 / a * t) = ‖B.det‖ ^ 2 * t := by field_simp
  rw [this]
  nlinarith

theorem gram_block {k d : Type*} [Fintype k] [DecidableEq k] [Fintype d] [DecidableEq d]
    (Uc : Matrix m k ℂ) (Zc Ac : Matrix m d ℂ) (T : Matrix (k ⊕ d) d ℂ)
    (hT : Ac = fromCols Uc Zc * T) (hAU : Acᴴ * Uc = 0) (hg : (Ucᴴ * Uc).det ≠ 0) :
    (Ucᴴ * Uc).det * ((Acᴴ * Zc).det * star (Acᴴ * Zc).det) =
      (Acᴴ * Ac).det * ((fromCols Uc Zc)ᴴ * fromCols Uc Zc).det := by
  set B := fromCols Uc Zc with hBdef
  set Rm : Matrix (k ⊕ d) (k ⊕ d) ℂ := fromBlocks 1 T.toRows₁ 0 T.toRows₂ with hRm
  have hBR : B * Rm = fromCols Uc Ac := by
    rw [hBdef, hRm, fromCols_mul_fromBlocks, hT, ← fromRows_toRows T, fromCols_mul_fromRows]
    simp
  have e1 : (fromCols Uc Ac)ᴴ * B = fromBlocks (Ucᴴ * Uc) (Ucᴴ * Zc) 0 (Acᴴ * Zc) := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, hBdef, fromRows_mul_fromCols, hAU]
  have e2 : (fromCols Uc Ac)ᴴ * fromCols Uc Ac =
      fromBlocks (Ucᴴ * Uc) (Ucᴴ * Ac) 0 (Acᴴ * Ac) := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols, hAU]
  have f1 : (Ucᴴ * Uc).det * (Acᴴ * Zc).det = star Rm.det * (Bᴴ * B).det := by
    rw [← det_fromBlocks_zero₂₁ (Ucᴴ * Uc) (Ucᴴ * Zc) (Acᴴ * Zc), ← e1, ← hBR]
    have : (B * Rm)ᴴ * B = Rmᴴ * (Bᴴ * B) := by rw [conjTranspose_mul, Matrix.mul_assoc]
    rw [this, det_mul, det_conjTranspose]
  have f2 : (Ucᴴ * Uc).det * (Acᴴ * Ac).det = star Rm.det * (Bᴴ * B).det * Rm.det := by
    rw [← det_fromBlocks_zero₂₁ (Ucᴴ * Uc) (Ucᴴ * Ac) (Acᴴ * Ac), ← e2, ← hBR]
    have : (B * Rm)ᴴ * (B * Rm) = Rmᴴ * (Bᴴ * B) * Rm := by
      rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [this, det_mul, det_mul, det_conjTranspose]
  have hgs : star (Ucᴴ * Uc).det = (Ucᴴ * Uc).det := by
    rw [← det_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
  have hGs : star (Bᴴ * B).det = (Bᴴ * B).det := by
    rw [← det_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
  set g := (Ucᴴ * Uc).det
  set p := (Acᴴ * Zc).det
  set a := (Acᴴ * Ac).det
  set G := (Bᴴ * B).det
  set r := Rm.det
  have h3 : g * star p = r * G := by
    have := congrArg star f1
    rw [star_mul', star_mul', hgs, hGs, star_star] at this
    linear_combination this
  apply mul_left_cancel₀ hg
  linear_combination (g * star p) * f1 + (star r * G) * h3 - G * f2

end Mat

section NF

open NumberField Formalism.BasicNotions PI.Dv

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def cmat (A : HLat K) (φ : K →+* ℂ) {m : ℕ} (f : Fin m → A.V) : Matrix A.ι (Fin m) ℂ :=
  Matrix.of fun k i => φ (A.b.repr (f i) k)

def hmat (A : HLat K) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) (φ : K →+* ℂ) : Matrix A.ι A.ι ℂ :=
  Matrix.of fun k l => φ (h (A.b k) (A.b l))

def rho (φ : K →+* ℂ) : K →+* ℂ := (starRingEnd ℂ).comp (φ.comp (starRingEnd K))

lemma rho_apply (φ : K →+* ℂ) (x : K) : rho φ x = star (φ (star x)) := rfl

def gmat (A : HLat K) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) (φ : K →+* ℂ) {m : ℕ} (f : Fin m → A.V) :
    Matrix (Fin m) (Fin m) ℂ :=
  (cmat A φ f)ᴴ * hmat A h φ * cmat A φ f

lemma gramPl_eq (A : HLat K) (v : InfinitePlace K) {m : ℕ} (f : Fin m → A.V) :
    Formalism.HN.gramPl A.b A.X v f =
      ((A.X v)⁻¹ * cmat A v.embedding f)ᴴ * ((A.X v)⁻¹ * cmat A v.embedding f) := by
  ext a c
  simp [Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, cmat, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, conjTranspose_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

lemma frame_majAt (A : HLat K) (v : InfinitePlace K) :
    ((A.X v)⁻¹)ᴴ * (A.X v)⁻¹ =
      Matrix.of fun k l => Formalism.HermitianLatticesTheory.majAt A.b A.X v (A.b k) (A.b l) := by
  ext k l
  simp [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, conjTranspose_apply, Finsupp.single_apply, apply_ite]

lemma h_expand (A : HLat K) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) (x y : A.V) :
    h x y = ∑ k, ∑ l, star (A.b.repr x k) * A.b.repr y l * h (A.b k) (A.b l) := by
  conv_lhs => rw [← A.b.sum_repr x, ← A.b.sum_repr y]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul,
    smul_eq_mul, starRingEnd_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma hmatrix_eq (A : HLat K) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) (φ : K →+* ℂ) {m m' : ℕ}
    (f : Fin m → A.V) (g : Fin m' → A.V) :
    (Matrix.of fun i j => φ (h (f i) (g j))) = (cmat A (rho φ) f)ᴴ * hmat A h φ * cmat A φ g := by
  ext i j
  simp only [of_apply, h_expand A h (f i) (g j), map_sum, map_mul, Matrix.mul_apply,
    conjTranspose_apply, cmat, hmat, rho_apply, star_star, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma map_det_of (φ : K →+* ℂ) {d : ℕ} (F : Fin d → Fin d → K) :
    φ (Matrix.of F).det = (Matrix.of fun i j => φ (F i j)).det := by
  rw [RingHom.map_det]; rfl

variable (A : HLat K) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K)

section Hyp

variable (hC1 : ∀ i j, IsCM (h (A.b i) (A.b j)))
  (hC3 : ∀ (v : InfinitePlace K) i j,
    Formalism.HermitianLatticesTheory.majAt A.b A.X v (A.b i) (A.b j) = v.embedding (h (A.b i) (A.b j)))
include hC3

lemma frame_hmat (v : InfinitePlace K) : ((A.X v)⁻¹)ᴴ * (A.X v)⁻¹ = hmat A h v.embedding := by
  rw [frame_majAt]; ext k l; simp [hmat, hC3]

lemma sigma_hmatrix (v : InfinitePlace K) {m m' : ℕ} (f : Fin m → A.V) (g : Fin m' → A.V) :
    (Matrix.of fun i j => v.embedding (h (f i) (g j))) =
      ((A.X v)⁻¹ * cmat A (rho v.embedding) f)ᴴ * ((A.X v)⁻¹ * cmat A v.embedding g) := by
  rw [hmatrix_eq, ← frame_hmat A h hC3, conjTranspose_mul]
  simp only [Matrix.mul_assoc]

lemma gmat_place (v : InfinitePlace K) {m : ℕ} (f : Fin m → A.V) :
    gmat A h v.embedding f = Formalism.HN.gramPl A.b A.X v f := by
  rw [gramPl_eq, gmat, ← frame_hmat A h hC3, conjTranspose_mul]
  simp only [Matrix.mul_assoc]

omit hC3 in
lemma gmat_conj (φ : K →+* ℂ) {m : ℕ} (f : Fin m → A.V) :
    gmat A h (ComplexEmbedding.conjugate φ) f = (gmat A h φ f).map (starRingEnd ℂ) := by
  ext i j
  simp [gmat, cmat, hmat, Matrix.mul_apply, conjTranspose_apply, map_sum]

omit hC3 in
lemma gramPl_psd (v : InfinitePlace K) {m : ℕ} (f : Fin m → A.V) :
    (Formalism.HN.gramPl A.b A.X v f).PosSemidef := by
  rw [gramPl_eq]; exact posSemidef_conjTranspose_mul_self _

lemma det_gmat (φ : K →+* ℂ) {m : ℕ} (f : Fin m → A.V) :
    (gmat A h φ f).det = (Formalism.HN.gramPl A.b A.X (InfinitePlace.mk φ) f).det := by
  have hreal := (psd_det_real (gramPl_psd A (InfinitePlace.mk φ) f)).1
  rcases InfinitePlace.embedding_mk_eq φ with h1 | h1
  · rw [← gmat_place A h hC3, h1]
  · have hφ : φ = ComplexEmbedding.conjugate (InfinitePlace.mk φ).embedding := by
      rw [h1]; ext x; simp
    conv_lhs => rw [hφ]
    rw [gmat_conj, ← RingHom.mapMatrix_apply, ← RingHom.map_det, gmat_place A h hC3, hreal]
    simp

omit hC3 in
include hC1 in
lemma hmat_rho (φ : K →+* ℂ) : hmat A h (rho φ) = hmat A h φ := by
  ext k l
  simp only [hmat, of_apply, rho_apply]
  rw [hC1 k l φ, star_star]

include hC1 in
lemma rhoGram_det (v : InfinitePlace K) {m : ℕ} (f : Fin m → A.V) :
    (((A.X v)⁻¹ * cmat A (rho v.embedding) f)ᴴ * ((A.X v)⁻¹ * cmat A (rho v.embedding) f)).det =
      (Formalism.HN.gramPl A.b A.X (InfinitePlace.mk (v.embedding.comp (starRingEnd K))) f).det := by
  have e1 : ((A.X v)⁻¹ * cmat A (rho v.embedding) f)ᴴ * ((A.X v)⁻¹ * cmat A (rho v.embedding) f) =
      gmat A h (rho v.embedding) f := by
    rw [gmat, hmat_rho A h hC1, ← frame_hmat A h hC3, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have e2 : rho v.embedding = ComplexEmbedding.conjugate (v.embedding.comp (starRingEnd K)) := by
    ext x
    simp only [rho_apply, ComplexEmbedding.conjugate_coe_eq, RingHom.coe_comp, Function.comp_apply,
      starRingEnd_apply]
  rw [e1, det_gmat A h hC3, e2, InfinitePlace.mk_conjugate_eq]

end Hyp

def piv (v : InfinitePlace K) : InfinitePlace K := InfinitePlace.mk (v.embedding.comp (starRingEnd K))

lemma piv_involutive : Function.Involutive (piv (K := K)) := by
  intro v
  simp only [piv]
  rcases InfinitePlace.embedding_mk_eq (v.embedding.comp (starRingEnd K)) with h1 | h1 <;> rw [h1]
  · have : (v.embedding.comp (starRingEnd K)).comp (starRingEnd K) = v.embedding := by
      ext x; simp
    rw [this, InfinitePlace.mk_embedding]
  · have : (ComplexEmbedding.conjugate (v.embedding.comp (starRingEnd K))).comp (starRingEnd K) =
        ComplexEmbedding.conjugate v.embedding := by
      ext x; simp [ComplexEmbedding.conjugate_coe_eq]
    rw [this, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

lemma sum_piv (F : InfinitePlace K → ℝ) : ∑ v, F (piv v) = ∑ v, F v :=
  Equiv.sum_comp (Function.Involutive.toPerm _ piv_involutive) F

lemma cmat_injective (A : HLat K) (σ : K →+* ℂ) {m : ℕ} (f : Fin m → A.V)
    (hf : LinearIndependent K f) : Function.Injective (cmat A σ f).mulVec := by
  set Y : Matrix A.ι (Fin m) K := Matrix.of fun k i => A.b.repr (f i) k with hY
  have hYc : ∀ c : Fin m → K, Y *ᵥ c = ⇑(A.b.repr (∑ i, c i • f i)) := by
    intro c; ext k
    simp [hY, Matrix.mulVec, dotProduct, map_sum, Finsupp.finsetSum_apply, mul_comm]
  have hker : LinearMap.ker (Matrix.mulVecLin Y) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    have h0 : A.b.repr (∑ i, c i • f i) = 0 := by
      ext k; have := congrFun hc k; rw [Matrix.mulVecLin_apply, hYc] at this; simpa using this
    have h1 : ∑ i, c i • f i = 0 := A.b.repr.injective (by rw [h0, map_zero])
    exact funext (Fintype.linearIndependent_iff.1 hf c h1)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  set L := LinearMap.toMatrix' g
  have hLY : L * Y = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    have hYY : LinearMap.toMatrix' (Matrix.mulVecLin Y) = Y := by
      ext i j; simp [LinearMap.toMatrix'_apply]
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, hYY] at this
  have hmap : L.map σ * cmat A σ f = 1 := by
    have : cmat A σ f = Y.map σ := by ext; simp [cmat, hY]
    rw [this, ← Matrix.map_mul, hLY, Matrix.map_one _ (map_zero σ) (map_one σ)]
  intro a b hab
  have := congrArg (L.map σ).mulVec hab
  simpa [mulVec_mulVec, hmap] using this

lemma gramPl_posDef (A : HLat K) (v : InfinitePlace K) (hX : IsUnit (A.X v).det) {m : ℕ}
    (f : Fin m → A.V) (hf : LinearIndependent K f) : (Formalism.HN.gramPl A.b A.X v f).PosDef := by
  rw [gramPl_eq]
  apply PosDef.conjTranspose_mul_self
  have hXi : Function.Injective ((A.X v)⁻¹).mulVec :=
    (mulVec_injective_iff_isUnit).2 ((isUnit_iff_isUnit_det _).2 (isUnit_nonsing_inv_det _ hX))
  intro a b hab
  simp only [← mulVec_mulVec] at hab
  exact cmat_injective A v.embedding f hf (hXi hab)

lemma gramPl_pos (A : HLat K) (v : InfinitePlace K) (hX : IsUnit (A.X v).det) {m : ℕ}
    (f : Fin m → A.V) (hf : LinearIndependent K f) : 0 < (Formalism.HN.gramPl A.b A.X v f).det.re :=
  (pd_det_real (gramPl_posDef A v hX f hf)).2

lemma log_abs_norm [IsTotallyComplex K] (x : K) (hx : x ≠ 0) :
    Real.log |((Algebra.norm ℚ x : ℚ) : ℝ)| = ∑ v : InfinitePlace K, 2 * Real.log ‖v.embedding x‖ := by
  have h := InfinitePlace.prod_eq_abs_norm x
  rw [← Rat.cast_abs, ← h, Real.log_prod]
  · refine Finset.sum_congr rfl fun v _ => ?_
    have hm : v.mult = 2 := InfinitePlace.mult_isComplex ⟨v, IsTotallyComplex.isComplex v⟩
    rw [Real.log_pow, InfinitePlace.norm_embedding_eq, hm]; push_cast; ring
  · intro v _
    exact pow_ne_zero _ (InfinitePlace.pos_iff.2 hx).ne'

lemma cmat_rho_range (A : HLat K) (e : Module.End K A.V) (he : e * e = e)
    (hCe : ∀ i j, IsCM (A.b.repr (e (A.b j)) i)) (σ : K →+* ℂ) {N m : ℕ} (w : Fin N → A.V)
    (hw : Submodule.span K (Set.range w) = LinearMap.range e) (y : Fin m → A.V)
    (hy : ∀ i, y i ∈ LinearMap.range e) :
    ∃ T0 : Matrix (Fin N) (Fin m) ℂ, cmat A (rho σ) y = cmat A σ w * T0 := by
  have hc : ∀ l, ∃ c : Fin N → K, ∑ j, c j • w j = e (A.b l) := fun l => by
    have : e (A.b l) ∈ Submodule.span K (Set.range w) := hw ▸ LinearMap.mem_range_self e _
    exact (Submodule.mem_span_range_iff_exists_fun K).1 this
  choose c hc using hc
  refine ⟨Matrix.of fun j i => ∑ l, σ (c l j) * rho σ (A.b.repr (y i) l), ?_⟩
  ext k i
  have hyi : e (y i) = y i := by
    obtain ⟨x, hx⟩ := hy i; rw [← hx, ← Module.End.mul_apply, he]
  have h1 : A.b.repr (y i) k = ∑ l, A.b.repr (e (A.b l)) k * A.b.repr (y i) l := by
    conv_lhs => rw [← hyi]
    rw [← LinearMap.toMatrix_mulVec_repr A.b A.b e]
    simp [Matrix.mulVec, dotProduct, LinearMap.toMatrix_apply]
  have h2 : ∀ l, A.b.repr (e (A.b l)) k = ∑ j, c l j * A.b.repr (w j) k := fun l => by
    rw [← hc l]; simp [map_sum, Finsupp.finsetSum_apply]
  have h3 : ∀ l, rho σ (A.b.repr (e (A.b l)) k) = σ (A.b.repr (e (A.b l)) k) := fun l => by
    rw [rho_apply, hCe k l σ, star_star]
  simp only [cmat, of_apply, Matrix.mul_apply]
  rw [h1, map_sum]
  simp_rw [map_mul, h3, h2, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end NF

end GramDeterminantPositive

open NumberField Formalism.BasicNotions PI.Dv GramDeterminantPositive Matrix

theorem gram_cauchy_schwarz : GramCS := by
  intro K _ _ _ _ _ A e n h hyp d y hy
  obtain ⟨hS, hP, _, hC1, _, hC3⟩ := hyp
  have hX : ∀ v, IsUnit (A.X v).det := hP.1.1
  set Hm : Matrix (Fin d) (Fin d) K := Matrix.of fun i j => h (y i) (y j) with hHm
  have hG : ∀ v, 0 < (Formalism.HN.gramPl A.b A.X v y).det.re := fun v => gramPl_pos A v (hX v) y hy
  have hσ : ∀ v : InfinitePlace K, v.embedding Hm.det =
      (((A.X v)⁻¹ * cmat A (rho v.embedding) y)ᴴ * ((A.X v)⁻¹ * cmat A v.embedding y)).det := by
    intro v; rw [hHm, map_det_of, sigma_hmatrix A h hC3]
  have hne : Hm.det ≠ 0 := by
    obtain ⟨σ0, hσ0⟩ := hS
    have hrho : rho (InfinitePlace.mk σ0).embedding = (InfinitePlace.mk σ0).embedding := by
      ext x
      rw [rho_apply]
      rcases InfinitePlace.embedding_mk_eq σ0 with h1 | h1 <;> rw [h1]
      · rw [hσ0, star_star]
      · simp [ComplexEmbedding.conjugate_coe_eq, hσ0]
    intro h0
    have h1 := hσ (InfinitePlace.mk σ0)
    rw [h0, map_zero, hrho, ← gramPl_eq] at h1
    have h2 := hG (InfinitePlace.mk σ0)
    rw [← h1] at h2
    simp at h2
  have hv : ∀ v : InfinitePlace K, 2 * Real.log ‖v.embedding Hm.det‖ ≤
      Real.log (Formalism.HN.gramPl A.b A.X (piv v) y).det.re +
        Real.log (Formalism.HN.gramPl A.b A.X v y).det.re := by
    intro v
    have hcs := gram_cs ((A.X v)⁻¹ * cmat A (rho v.embedding) y) ((A.X v)⁻¹ * cmat A v.embedding y)
    rw [← hσ v, rhoGram_det A h hC1 hC3, ← gramPl_eq] at hcs
    have hpos : 0 < ‖v.embedding Hm.det‖ := norm_pos_iff.2 ((map_ne_zero _).2 hne)
    rw [← Real.log_mul (hG _).ne' (hG _).ne']
    have h2 : 2 * Real.log ‖v.embedding Hm.det‖ = Real.log (‖v.embedding Hm.det‖ ^ 2) := by
      rw [Real.log_pow]; norm_num
    rw [h2]
    exact Real.log_le_log (by positivity) hcs
  refine ⟨hne, ?_⟩
  rw [log_abs_norm _ hne]
  calc ∑ v, 2 * Real.log ‖v.embedding Hm.det‖
      ≤ ∑ v, (Real.log (Formalism.HN.gramPl A.b A.X (piv v) y).det.re +
          Real.log (Formalism.HN.gramPl A.b A.X v y).det.re) := Finset.sum_le_sum fun v _ => hv v
    _ = 2 * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v y).det.re := by
        rw [Finset.sum_add_distrib, sum_piv (fun v => Real.log (Formalism.HN.gramPl A.b A.X v y).det.re)]
        ring

theorem archimedean_identity : ArchIdentity := by
  intro K _ _ _ _ _ A e n h hyp U hU k d u z y hli hspan hu hy hyr hyU
  obtain ⟨_, hP, _, hC1, hC2, hC3⟩ := hyp
  have hX : ∀ v, IsUnit (A.X v).det := hP.1.1
  have he : e * e = e := hP.2.2.1
  have hu_li : LinearIndependent K u := by
    have := hli.comp (Fin.castAdd d) (Fin.castAdd_injective k d)
    convert this using 1
    funext i; simp
  set Hm : Matrix (Fin d) (Fin d) K := Matrix.of fun i j => h (y i) (z j) with hHm
  have hv : ∀ v : InfinitePlace K,
      Real.log (Formalism.HN.gramPl A.b A.X v (Fin.append u z)).det.re -
        Real.log (Formalism.HN.gramPl A.b A.X v u).det.re +
        Real.log (Formalism.HN.gramPl A.b A.X (piv v) y).det.re = 2 * Real.log ‖v.embedding Hm.det‖ := by
    intro v
    set Uc := (A.X v)⁻¹ * cmat A v.embedding u with hUc
    set Zc := (A.X v)⁻¹ * cmat A v.embedding z with hZc
    set Ac := (A.X v)⁻¹ * cmat A (rho v.embedding) y with hAc
    set Wc := (A.X v)⁻¹ * cmat A v.embedding (Fin.append u z) with hWc
    have hAU : Acᴴ * Uc = 0 := by
      rw [hAc, hUc, ← sigma_hmatrix A h hC3]
      ext i j
      simp only [of_apply, Matrix.zero_apply]
      rw [hyU i (u j) (hu ▸ Submodule.subset_span ⟨j, rfl⟩), map_zero]
    obtain ⟨T0, hT0⟩ := cmat_rho_range A e he hC2 v.embedding (Fin.append u z) hspan y hyr
    have hB : fromCols Uc Zc = Wc.submatrix id finSumFinEquiv := by
      ext i j; rcases j with j | j <;> simp [hUc, hZc, hWc, cmat, Matrix.mul_apply]
    have hT : Ac = fromCols Uc Zc * T0.submatrix finSumFinEquiv id := by
      rw [hB, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, hAc, hWc, hT0, Matrix.mul_assoc]
    have hgu := pd_det_real (gramPl_posDef A v (hX v) u hu_li)
    have hgw := pd_det_real (gramPl_posDef A v (hX v) _ hli)
    have hgy := pd_det_real (gramPl_posDef A (piv v) (hX _) y hy)
    have hUU : Ucᴴ * Uc = Formalism.HN.gramPl A.b A.X v u := by rw [gramPl_eq]
    have hg : (Ucᴴ * Uc).det ≠ 0 := by
      rw [hUU, hgu.1]; exact_mod_cast hgu.2.ne'
    have key := gram_block Uc Zc Ac _ hT hAU hg
    have hBB : ((fromCols Uc Zc)ᴴ * fromCols Uc Zc).det =
        (Formalism.HN.gramPl A.b A.X v (Fin.append u z)).det := by
      rw [hB, gramPl_eq, ← hWc]
      have : (Wc.submatrix id finSumFinEquiv)ᴴ * Wc.submatrix id finSumFinEquiv =
          (Wcᴴ * Wc).submatrix finSumFinEquiv finSumFinEquiv := by
        ext p q; simp [Matrix.mul_apply, conjTranspose_apply]
      rw [this, det_submatrix_equiv_self]
    have hAA : (Acᴴ * Ac).det = (Formalism.HN.gramPl A.b A.X (piv v) y).det := by
      rw [hAc]; exact rhoGram_det A h hC1 hC3 v y
    have hAZ : (Acᴴ * Zc).det = v.embedding Hm.det := by
      rw [hAc, hZc, ← sigma_hmatrix A h hC3, hHm, map_det_of]
    rw [hUU, hBB, hAA, hAZ, hgu.1, hgy.1, hgw.1, Complex.star_def, Complex.mul_conj'] at key
    set p := v.embedding Hm.det
    have key' : (Formalism.HN.gramPl A.b A.X v u).det.re * ‖p‖ ^ 2 =
        (Formalism.HN.gramPl A.b A.X (piv v) y).det.re *
          (Formalism.HN.gramPl A.b A.X v (Fin.append u z)).det.re := by
      exact_mod_cast key
    have hp : 0 < ‖p‖ := by
      by_contra hp0
      have : ‖p‖ = 0 := le_antisymm (not_lt.1 hp0) (norm_nonneg _)
      rw [this] at key'
      have := mul_pos hgy.2 hgw.2
      nlinarith
    have hl := congrArg Real.log key'
    rw [Real.log_mul hgu.2.ne' (by positivity), Real.log_mul hgy.2.ne' hgw.2.ne', Real.log_pow] at hl
    push_cast at hl
    linarith
  have hsum : ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v (Fin.append u z)).det.re -
        ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v u).det.re +
        ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v y).det.re =
      ∑ v : InfinitePlace K, 2 * Real.log ‖v.embedding Hm.det‖ := by
    rw [← sum_piv (fun v => Real.log (Formalism.HN.gramPl A.b A.X v y).det.re), ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => hv v
  rw [hsum]
  by_cases hD : Hm.det = 0
  · rw [hD]; simp [Algebra.norm_zero]
  · rw [log_abs_norm _ hD]

end PI.DvRows
