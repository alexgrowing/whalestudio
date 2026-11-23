import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.Published

def Landherr : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (G G' : Matrix (Fin r) (Fin r) E),
    (∀ a b, cc (G a b) = G b a) → (∀ a b, cc (G' a b) = G' b a) →
    G.det ≠ 0 → G'.det ≠ 0 →
    (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      G'.map τ = Qᵀ * G.map τ * Q.map conj) →
    (∃ x : E, G.det / G'.det = x * cc x) →
    ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map cc

def HasseNorm : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] (a : K), a ≠ 0 →
    (∀ v : HeightOneSpectrum (𝓞 K), ∃ z : v.adicCompletion K ⊗[K] L,
      Algebra.norm (v.adicCompletion K) z = algebraMap K (v.adicCompletion K) a) →
    (∀ v : InfinitePlace K, ∃ z : v.Completion ⊗[K] L,
      Algebra.norm v.Completion z = algebraMap K v.Completion a) →
    ∃ x : L, Algebra.norm K x = a

section Basic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_col (G P : Matrix (Fin r) (Fin r) E) (a b : Fin r) :
    herm G (fun k => P k a) (fun k => P k b) = (Pᵀ * G * P.map cc) a b := by
  simp only [herm, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_comm

omit [NumberField E] [IsCMField E] in

theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (Q : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G Q = Qᵀ * G.map τ * Q.map conj := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem map_cc_eq (P : Matrix (Fin r) (Fin r) E) :
    P.map cc = (IsCMField.complexConj E : E →+* E).mapMatrix P := rfl

theorem det_map_cc (P : Matrix (Fin r) (Fin r) E) : (P.map cc).det = cc P.det := by
  rw [map_cc_eq, ← RingHom.map_det]; rfl

theorem embedding_cc (τ : E →+* ℂ) (x : E) : τ (cc x) = conj (τ x) :=
  IsCMField.complexEmbedding_complexConj E τ x

theorem cc_ne_zero {x : E} (hx : x ≠ 0) : cc x ≠ 0 := by
  simpa [cc] using hx

theorem cc_det_of_herm {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, cc (G a b) = G b a) :
    cc G.det = G.det := by
  rw [← det_map_cc, ← Matrix.det_transpose G]
  congr 1
  ext a b
  exact hG a b

end Basic

namespace Landherr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {G G' : Matrix (Fin r) (Fin r) E}

theorem congr_complex (h : ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map cc)
    (τ : E →+* ℂ) :
    ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ G'.map τ = Qᵀ * G.map τ * Q.map conj := by
  obtain ⟨P, hP, rfl⟩ := h
  refine ⟨P.map τ, ?_, ?_⟩
  · have : (P.map τ).det = τ P.det := (RingHom.map_det τ P).symm
    rw [this]
    exact (map_ne_zero τ).mpr hP
  · rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    congr 1
    ext a b
    exact embedding_cc τ _

theorem det_norm (hG : G.det ≠ 0)
    (h : ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map cc) :
    ∃ x : E, G.det / G'.det = x * cc x := by
  obtain ⟨P, hP, rfl⟩ := h
  refine ⟨P.det⁻¹, ?_⟩
  have h1 : cc P.det⁻¹ = (cc P.det)⁻¹ := by simp [cc]
  have h2 := cc_ne_zero hP
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_map_cc, h1]
  field_simp

theorem iff (H : Landherr) (hG : ∀ a b, cc (G a b) = G b a) (hG' : ∀ a b, cc (G' a b) = G' b a)
    (hd : G.det ≠ 0) (hd' : G'.det ≠ 0) :
    (∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map cc) ↔
      (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
        G'.map τ = Qᵀ * G.map τ * Q.map conj) ∧ ∃ x : E, G.det / G'.det = x * cc x :=
  ⟨fun h => ⟨congr_complex h, det_norm hd h⟩, fun h => H E r G G' hG hG' hd hd' h.1 h.2⟩

theorem size_zero (G G' : Matrix (Fin 0) (Fin 0) E) :
    ∃ P : Matrix (Fin 0) (Fin 0) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map cc :=
  ⟨1, by simp, Subsingleton.elim _ _⟩

theorem size_one (G G' : Matrix (Fin 1) (Fin 1) E) (hd : G.det ≠ 0) (hd' : G'.det ≠ 0)
    (h : ∃ x : E, G.det / G'.det = x * cc x) :
    ∃ P : Matrix (Fin 1) (Fin 1) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map cc := by
  obtain ⟨x, hx⟩ := h
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact div_ne_zero hd hd' (by simpa using hx)
  have hc := cc_ne_zero hx0
  have h1 : cc x⁻¹ = (cc x)⁻¹ := by simp [cc]
  rw [Matrix.det_fin_one] at hd hd'
  rw [Matrix.det_fin_one, Matrix.det_fin_one, div_eq_iff hd'] at hx
  refine ⟨!![x⁻¹], by simpa using hx0, ?_⟩
  ext a b
  fin_cases a; fin_cases b
  simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.transpose_apply, Matrix.map_apply,
    Fin.zero_eta, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, h1, hx]
  field_simp

omit [NumberField E] [IsCMField E] in

theorem congr_of_gram_eq (τ : E →+* ℂ) {Q Q' : Matrix (Fin r) (Fin r) ℂ} (hQ : Q.det ≠ 0)
    (hQ' : Q'.det ≠ 0) (h : gram τ G Q = gram τ G' Q') :
    ∃ R : Matrix (Fin r) (Fin r) ℂ, R.det ≠ 0 ∧ G'.map τ = Rᵀ * G.map τ * R.map conj := by
  rw [gram_eq, gram_eq] at h
  have hu : IsUnit Q'.det := isUnit_iff_ne_zero.mpr hQ'
  refine ⟨Q * Q'⁻¹, ?_, ?_⟩
  · rw [Matrix.det_mul]
    exact mul_ne_zero hQ (Matrix.isUnit_nonsing_inv_det _ hu).ne_zero
  · have e1 : Q'⁻¹ᵀ * Q'ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.transpose_one]
    have e2 : Q'.map conj * Q'⁻¹.map conj = 1 := by
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
    calc G'.map τ = (Q'⁻¹ᵀ * Q'ᵀ) * G'.map τ * (Q'.map conj * Q'⁻¹.map conj) := by
          rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
      _ = Q'⁻¹ᵀ * (Q'ᵀ * G'.map τ * Q'.map conj) * Q'⁻¹.map conj := by
          simp only [Matrix.mul_assoc]
      _ = (Q * Q'⁻¹)ᵀ * G.map τ * (Q * Q'⁻¹).map conj := by
          rw [← h, Matrix.transpose_mul, Matrix.map_mul]
          simp only [Matrix.mul_assoc]

omit [NumberField E] [IsCMField E] in

theorem congr_conjugate (τ : E →+* ℂ)
    (h : ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ G'.map τ = Qᵀ * G.map τ * Q.map conj) :
    ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ G'.map (ComplexEmbedding.conjugate τ) =
      Qᵀ * G.map (ComplexEmbedding.conjugate τ) * Q.map conj := by
  obtain ⟨Q, hQ, h⟩ := h
  refine ⟨Q.map conj, ?_, ?_⟩
  · have : (Q.map conj).det = conj Q.det := (RingHom.map_det (starRingEnd ℂ) Q).symm
    rw [this]
    exact (map_ne_zero _).mpr hQ
  · have e : ∀ M : Matrix (Fin r) (Fin r) E,
        M.map (ComplexEmbedding.conjugate τ) = (M.map τ).map conj := fun M => rfl
    rw [e, e, h, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]

omit [NumberField E] [IsCMField E] in

theorem congr_of_signature (Ψ : Set (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ∨ ComplexEmbedding.conjugate τ ∈ Ψ)
    (hs : ∀ τ ∈ Ψ, ∃ p : ℕ,
      (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
        gram τ G Q = Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) ∧
      ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
        gram τ G' Q = Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ))
    (τ : E →+* ℂ) :
    ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ G'.map τ = Qᵀ * G.map τ * Q.map conj := by
  have key : ∀ σ ∈ Ψ, ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      G'.map σ = Qᵀ * G.map σ * Q.map conj := by
    intro σ hσ
    obtain ⟨p, ⟨Q, hQ, h⟩, Q', hQ', h'⟩ := hs σ hσ
    exact congr_of_gram_eq σ hQ hQ' (h.trans h'.symm)
  rcases hΨ τ with h | h
  · exact key τ h
  · have := congr_conjugate _ (key _ h)
    rwa [show ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ from star_star τ] at this

theorem of_signature (H : Landherr) (hG : ∀ a b, cc (G a b) = G b a)
    (hG' : ∀ a b, cc (G' a b) = G' b a) (hd : G.det ≠ 0) (hd' : G'.det ≠ 0)
    (Ψ : Set (E →+* ℂ)) (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ∨ ComplexEmbedding.conjugate τ ∈ Ψ)
    (hs : ∀ τ ∈ Ψ, ∃ p : ℕ,
      (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
        gram τ G Q = Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) ∧
      ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
        gram τ G' Q = Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ))
    (hn : ∃ x : E, G.det / G'.det = x * cc x) :
    ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map cc :=
  H E r G G' hG hG' hd hd' (congr_of_signature Ψ hΨ hs) hn

omit [NumberField E] [IsCMField E] in

theorem re_det_div_pos (hd : G.det ≠ 0) (τ : E →+* ℂ)
    (h : ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ G'.map τ = Qᵀ * G.map τ * Q.map conj) :
    0 < (τ (G.det / G'.det)).re := by
  obtain ⟨Q, hQ, h⟩ := h
  have e : ∀ M : Matrix (Fin r) (Fin r) E, (M.map τ).det = τ M.det :=
    fun M => (RingHom.map_det τ M).symm
  have e' : (Q.map conj).det = conj Q.det := (RingHom.map_det (starRingEnd ℂ) Q).symm
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, e, e, e'] at h2
  have hτ : τ G.det ≠ 0 := (map_ne_zero τ).mpr hd
  have hc : conj Q.det ≠ 0 := (map_ne_zero _).mpr hQ
  have h3 : τ (G.det / G'.det) = (((Complex.normSq Q.det)⁻¹ : ℝ) : ℂ) := by
    rw [map_div₀, h2, Complex.ofReal_inv, ← Complex.mul_conj]
    field_simp
  rw [h3, Complex.ofReal_re]
  exact inv_pos.mpr (Complex.normSq_pos.mpr hQ)

end Landherr

section QuadraticNorm

variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]

theorem norm_of_basis_one_sqrt (b : Module.Basis (Fin 2) A S) (h0 : b 0 = 1) (d : A)
    (h1 : b 1 * b 1 = algebraMap A S d) (x y : A) :
    Algebra.norm A (x • b 0 + y • b 1) = x ^ 2 - d * y ^ 2 := by
  have e0 : (x • b 0 + y • b 1) * b 0 = x • b 0 + y • b 1 := by rw [h0, mul_one]
  have e1 : (x • b 0 + y • b 1) * b 1 = (y * d) • b 0 + x • b 1 := by
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, h1, h0, one_mul, Algebra.algebraMap_eq_smul_one,
      smul_smul, add_comm]
  rw [Algebra.norm_eq_matrix_det b, Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, e0, e1, map_add, map_smul, Module.Basis.repr_self,
    Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply]
  simp
  ring

theorem algebraMap_norm_of_basis_one_sqrt (b : Module.Basis (Fin 2) A S) (h0 : b 0 = 1) (d : A)
    (h1 : b 1 * b 1 = algebraMap A S d) (σ : S →ₐ[A] S) (hσ : σ (b 1) = -b 1) (z : S) :
    algebraMap A S (Algebra.norm A z) = z * σ z := by
  have hz : z = b.repr z 0 • b 0 + b.repr z 1 • b 1 := by
    conv_lhs => rw [← b.sum_repr z, Fin.sum_univ_two]
  generalize b.repr z 0 = x, b.repr z 1 = y at hz
  subst hz
  rw [norm_of_basis_one_sqrt b h0 d h1, map_add, map_smul, map_smul, hσ, h0, map_one σ]
  simp only [Algebra.smul_def, map_sub, map_mul, map_pow, ← h1]
  ring

end QuadraticNorm

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

variable (E) in

theorem exists_cc_eq_neg : ∃ θ : E, θ ≠ 0 ∧ cc θ = -θ := by
  obtain ⟨x, hx⟩ : ∃ x : E, IsCMField.complexConj E x ≠ x := by
    by_contra h
    push Not at h
    exact IsCMField.complexConj_ne_one E (AlgEquiv.ext h)
  exact ⟨x - cc x, sub_ne_zero.mpr hx.symm, by simp [cc]⟩

theorem exists_basis_one_imaginary {θ : E} (h0 : θ ≠ 0) (hθ : cc θ = -θ) :
    ∃ b : Module.Basis (Fin 2) (maximalRealSubfield E) E, b 0 = 1 ∧ b 1 = θ := by
  have hli : LinearIndependent (maximalRealSubfield E) ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : (s : E) + (t : E) * θ = 0 := by
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      exact hst
    have h2 : (s : E) - (t : E) * θ = 0 := by
      have := congrArg (IsCMField.complexConj E) h1
      rw [map_add, map_mul, IsCMField.complexConj_apply_eq_self,
        IsCMField.complexConj_apply_eq_self, map_zero,
        show IsCMField.complexConj E θ = -θ from hθ] at this
      linear_combination this
    have hs : (s : E) = 0 := by linear_combination (h1 + h2) / 2
    have ht : (t : E) * θ = 0 := by linear_combination h1 - hs
    exact ⟨by exact_mod_cast hs, by exact_mod_cast (mul_eq_zero.mp ht).resolve_right h0⟩
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli
    (by rw [Algebra.IsQuadraticExtension.finrank_eq_two]; simp), ?_, ?_⟩ <;> simp

theorem exists_sq_real {θ : E} (hθ : cc θ = -θ) :
    ∃ d : maximalRealSubfield E, (d : E) = θ * θ :=
  ⟨⟨θ * θ, (IsCMField.complexConj_eq_self_iff E _).mp (by
    rw [map_mul, show IsCMField.complexConj E θ = -θ from hθ]; ring)⟩, rfl⟩

theorem coe_norm_eq_mul_cc (x : E) :
    ((Algebra.norm (maximalRealSubfield E) x : maximalRealSubfield E) : E) = x * cc x := by
  obtain ⟨θ, h0, hθ⟩ := exists_cc_eq_neg E
  obtain ⟨b, hb0, hb1⟩ := exists_basis_one_imaginary h0 hθ
  obtain ⟨d, hd⟩ := exists_sq_real hθ
  exact algebraMap_norm_of_basis_one_sqrt b hb0 d (by rw [hb1]; exact hd.symm)
    (IsCMField.complexConj E).toAlgHom (by rw [hb1]; exact hθ) x

variable (A : Type*) [CommRing A] [Algebra (maximalRealSubfield E) A]

theorem norm_tmul_add_tmul {θ : E} (h0 : θ ≠ 0) (hθ : cc θ = -θ) {d : maximalRealSubfield E}
    (hd : (d : E) = θ * θ) (x y : A) :
    Algebra.norm A (x ⊗ₜ[maximalRealSubfield E] (1 : E) + y ⊗ₜ[maximalRealSubfield E] θ) =
      x ^ 2 - algebraMap (maximalRealSubfield E) A d * y ^ 2 := by
  obtain ⟨b, hb0, hb1⟩ := exists_basis_one_imaginary h0 hθ
  have := norm_of_basis_one_sqrt (Algebra.TensorProduct.basis A b)
    (by rw [Algebra.TensorProduct.basis_apply, hb0]; rfl) (algebraMap _ A d)
    (by
      rw [Algebra.TensorProduct.basis_apply, hb1, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hd,
        ← IsScalarTower.algebraMap_apply]
      exact (Algebra.TensorProduct.algebraMap_apply' d).symm) x y
  rwa [Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply, hb0, hb1,
    TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_one,
    mul_one] at this

theorem algebraMap_norm_tensor (z : A ⊗[maximalRealSubfield E] E) :
    algebraMap A (A ⊗[maximalRealSubfield E] E) (Algebra.norm A z) =
      z * Algebra.TensorProduct.map (AlgHom.id A A) (IsCMField.complexConj E).toAlgHom z := by
  obtain ⟨θ, h0, hθ⟩ := exists_cc_eq_neg E
  obtain ⟨b, hb0, hb1⟩ := exists_basis_one_imaginary h0 hθ
  obtain ⟨d, hd⟩ := exists_sq_real hθ
  refine algebraMap_norm_of_basis_one_sqrt (Algebra.TensorProduct.basis A b)
    (by rw [Algebra.TensorProduct.basis_apply, hb0]; rfl) (algebraMap _ A d) ?_ _ ?_ z
  · rw [Algebra.TensorProduct.basis_apply, hb1, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hd,
      ← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.algebraMap_apply' d).symm
  · rw [Algebra.TensorProduct.basis_apply, hb1, Algebra.TensorProduct.map_tmul,
      ← TensorProduct.tmul_neg, ← hθ]
    rfl

end CM

namespace HasseNorm

theorem local_of_global {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (A : Type*) [CommRing A] [Algebra K A] {a : K} (h : ∃ x : L, Algebra.norm K x = a) :
    ∃ z : A ⊗[K] L, Algebra.norm A z = algebraMap K A a := by
  obtain ⟨x, rfl⟩ := h
  refine ⟨1 ⊗ₜ x, ?_⟩
  rw [Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange]
  congr 1
  exact (Algebra.baseChange_lmul x).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem infinite_of_pos (a : maximalRealSubfield E) (ha : ∀ τ : E →+* ℂ, 0 < (τ a).re)
    (v : InfinitePlace (maximalRealSubfield E)) :
    ∃ z : v.Completion ⊗[maximalRealSubfield E] E,
      Algebra.norm v.Completion z = algebraMap (maximalRealSubfield E) v.Completion a := by
  have hv : v.IsReal := IsTotallyReal.isReal v
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hv
  have he : e (algebraMap _ v.Completion a) = InfinitePlace.embedding_of_isReal hv a :=
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hv ((WithAbs.equiv v.1).symm a)
  have hpos : 0 < InfinitePlace.embedding_of_isReal hv a := by
    have h1 := ha (ComplexEmbedding.lift E v.embedding)
    have h2 : ComplexEmbedding.lift E v.embedding (a : E) = v.embedding a :=
      ComplexEmbedding.lift_algebraMap_apply E v.embedding a
    rwa [h2, ← InfinitePlace.embedding_of_isReal_apply hv, Complex.ofReal_re] at h1
  obtain ⟨θ, h0, hθ⟩ := exists_cc_eq_neg E
  obtain ⟨d, hd⟩ := exists_sq_real hθ
  refine ⟨_, (norm_tmul_add_tmul v.Completion h0 hθ hd
    (e.symm (Real.sqrt (InfinitePlace.embedding_of_isReal hv a))) 0).trans ?_⟩
  apply e.injective
  rw [he, zero_pow two_ne_zero, mul_zero, sub_zero, map_pow, e.apply_symm_apply, Real.sq_sqrt hpos.le]

theorem cm (H : HasseNorm) (a : maximalRealSubfield E) (ha : ∀ τ : E →+* ℂ, 0 < (τ a).re)
    (hf : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      ∃ z : v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] E,
        Algebra.norm (v.adicCompletion (maximalRealSubfield E)) z =
          algebraMap (maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E)) a) :
    ∃ x : E, (a : E) = x * cc x := by
  have : IsCyclic (E ≃ₐ[maximalRealSubfield E] E) :=
    isCyclic_iff_exists_zpowers_eq_top.mpr ⟨_, IsCMField.zpowers_complexConj_eq_top E⟩
  have h0 : a ≠ 0 := by
    rintro rfl
    simpa using ha (Classical.choice inferInstance)
  obtain ⟨x, hx⟩ := H (maximalRealSubfield E) E a h0 hf (infinite_of_pos a ha)
  exact ⟨x, by rw [← hx, coe_norm_eq_mul_cc]⟩

end HasseNorm

section Tests

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

end Tests

end GlobalTheory.Published
