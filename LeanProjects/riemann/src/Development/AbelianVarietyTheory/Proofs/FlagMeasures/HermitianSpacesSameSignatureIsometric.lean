import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPositiveAdd
import Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds

open NumberField Matrix

namespace GlobalTheory.FlagMeas

open ReciprocityTheory.ChartRestriction.G.FD

theorem exists_congr_of_hasSignature {n p q : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.UG.HasSignature M p q) (f : Fin n ≃ Fin p ⊕ Fin q) :
    ∃ A : Matrix (Fin n) (Fin n) ℂ, A.det ≠ 0 ∧
      Aᵀ * Mᵀ * A.map (starRingEnd ℂ) = ((Formalism.UG.Jpq p q).submatrix f f)ᵀ := by
  obtain ⟨e, P, hP⟩ := h
  have hPu : IsUnit (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 P.isUnit
  refine ⟨(P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e f, ?_, ?_⟩
  · have hσ : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e f =
        ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix f f).submatrix (e.trans f.symm) id := by
      ext i j; simp
    rw [hσ, Matrix.det_permute, Matrix.det_submatrix_equiv_self]
    exact mul_ne_zero (by simp) hPu.ne_zero
  · have hM : M = (M.reindex e e).submatrix e e := by ext i j; simp
    have hA : ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e f)ᴴ * M *
        (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e f = (Formalism.UG.Jpq p q).submatrix f f := by
      rw [hM, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, ← hP]
      congr 1
    rw [← hA]
    simp [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.conjTranspose]
    rfl

theorem sameKindIsometric : SameKindIsometric := by
  intro E _ _ _ hE n J J' hJ hJ' hd hd' hΛ hΛ' hsig
  obtain ⟨hTC, hφ, hun⟩ := hE
  have hne : ∃ z : E, star z ≠ z := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    have hc := hTC.isComplex w
    rw [InfinitePlace.isComplex_iff] at hc
    apply hc
    rw [ComplexEmbedding.isReal_iff]
    ext z
    rw [ComplexEmbedding.conjugate_coe_eq, ← hφ, hcon]
  obtain ⟨hcm, hst⟩ := (GlobalTheory.LeastExponentCompare.conj_iff E star).1
    ⟨fun φ z => by rw [hφ]; rfl, hne⟩
  have := hcm
  have hcc : ∀ z : E, star z = cc z := fun z => congrFun hst z
  have : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) := by
    refine Formalism.L2.Pj.unramBridge_holds E fun P hP => ?_
    obtain ⟨θ, t, ht, hθ⟩ := hun P hP
    refine ⟨θ, ?_⟩
    convert hθ using 2
    ext
    simp [ht, hcc, cc]
  have hform : ∀ (M : Matrix (Fin n) (Fin n) E) (x y : Fin n → E),
      ReciprocityTheory.ChartRestriction.G.FD.herm Mᵀ x y = star y ⬝ᵥ (M *ᵥ x) := by
    intro M x y
    simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.transpose_apply, Pi.star_apply, hcc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hone : ∀ z : E, z ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ↔ z ∈ (algebraMap (𝓞 E) E).range := by
    intro z
    rw [FractionalIdeal.mem_one_iff, RingHom.mem_range]
  have hmod : ∀ (M : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)),
      (∀ x, x ∈ L ↔ ∀ y ∈ L, star y ⬝ᵥ (M *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) →
      ∀ x, x ∈ L ↔ ∀ y ∈ L, ReciprocityTheory.ChartRestriction.G.FD.herm Mᵀ x y ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
    intro M L h x
    simp only [hone, hform]
    exact h x
  have hherm : ∀ M : Matrix (Fin n) (Fin n) E, Mᴴ = M → ∀ a b, cc (Mᵀ a b) = Mᵀ b a := by
    intro M hM a b
    rw [← hcc]
    have := congrFun (congrFun hM a) b
    simpa [Matrix.conjTranspose_apply] using this
  have hc : ∀ z ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), cc z ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
    intro z hz
    rw [FractionalIdeal.mem_one_iff] at hz ⊢
    obtain ⟨x, rfl⟩ := hz
    exact ⟨IsCMField.ringOfIntegersComplexConj E x, by simp [cc]⟩
  have hs : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧
      J'ᵀ.map τ = Qᵀ * Jᵀ.map τ * Q.map (starRingEnd ℂ) := by
    intro τ
    obtain ⟨p, q, h1, h2⟩ := hsig τ
    obtain ⟨e, -, -⟩ := id h1
    obtain ⟨A, hA, hA'⟩ := exists_congr_of_hasSignature h1 e
    obtain ⟨B, hB, hB'⟩ := exists_congr_of_hasSignature h2 e
    have hBi : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.2 hB)
    refine ⟨A * B⁻¹, by simp [Matrix.det_nonsing_inv, hA, hB], ?_⟩
    rw [Matrix.transpose_map, Matrix.transpose_map]
    have h1' : (B⁻¹)ᵀ * Bᵀ = 1 := by rw [← Matrix.transpose_mul, hBi, Matrix.transpose_one]
    have h2' : B.map (starRingEnd ℂ) * (B⁻¹).map (starRingEnd ℂ) = 1 := by
      rw [← Matrix.map_mul, hBi]
      simp
    have hY : (J'.map τ)ᵀ = (B⁻¹)ᵀ * (Bᵀ * (J'.map τ)ᵀ * B.map (starRingEnd ℂ)) *
        (B⁻¹).map (starRingEnd ℂ) := by
      simp only [← Matrix.mul_assoc]
      rw [h1', Matrix.one_mul, Matrix.mul_assoc, h2', Matrix.mul_one]
    rw [hY, hB', ← hA', Matrix.transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  obtain ⟨Λ, hΛl, hΛm⟩ := hΛ
  obtain ⟨Λ', hΛl', hΛm'⟩ := hΛ'
  obtain ⟨P, hPd, hP⟩ := GlobalTheory.SelfDualGenus.congr_of_modular
    (GlobalTheory.LocalQuad.landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt) GlobalTheory.QNorm.hasseNormSt
    (by
      intro h
      have h1 : (1 : E) ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
        rw [FractionalIdeal.mem_one_iff]
        exact ⟨1, map_one _⟩
      rw [h, FractionalIdeal.mem_zero_iff] at h1
      exact one_ne_zero h1) hc (hherm J hJ) (hherm J' hJ') (by rwa [Matrix.det_transpose])
    (by rwa [Matrix.det_transpose]) ⟨hΛl.fg, hΛl.span_eq_top⟩ ⟨hΛl'.fg, hΛl'.span_eq_top⟩
    (hmod J Λ hΛm) (hmod J' Λ' hΛm') hs
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero P hPd, ?_⟩
  have hT := congrArg Matrix.transpose hP
  rw [Matrix.transpose_transpose, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_transpose] at hT
  change Pᴴ * J * P = J'
  rw [hT, Matrix.mul_assoc]
  congr 1
  ext i j
  simp [Matrix.conjTranspose_apply, hcc]

end GlobalTheory.FlagMeas
