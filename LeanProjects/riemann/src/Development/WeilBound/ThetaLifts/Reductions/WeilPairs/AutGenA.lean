import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutDef
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryMatrixEqProdQuasiReflections
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryQuasiReflectionLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaFunNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionCommQuasiReflectionStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealSymplecticFormAlternatingInvariantDefinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHalfAbstract

set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct Matrix Kronecker Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix Formalism.IndefR.DatumF

namespace PositivityTheory.ThKW.GenA

section Abstract

theorem det_unit_sig {K ι G : Type} [Field K] [Fintype ι] [DecidableEq ι] [FunLike G K K] [RingHomClass G K K] (σ : G)
    {M P : Matrix ι ι K} (hP : P.det ≠ 0) (h : (M.map σ)ᵀ * P * M = P) :
    M.det * σ M.det = 1 ∧ M.det * σ (M - 1).det = (-1) ^ Fintype.card ι * (M - 1).det := by
  have hd : ∀ N : Matrix ι ι K, (N.map σ)ᵀ.det = σ N.det := fun N => by
    rw [det_transpose]; exact (RingHom.map_det (σ : K →+* K) N).symm
  constructor
  · have := congrArg Matrix.det h
    rw [det_mul, det_mul, hd] at this
    refine mul_right_cancel₀ hP ?_
    linear_combination this
  · have hm : (M - 1).map σ = M.map σ - 1 := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    have e : ((M - 1).map σ)ᵀ * P * M = P * -(M - 1) := by
      rw [hm, transpose_sub, transpose_one, Matrix.sub_mul, Matrix.sub_mul, h, Matrix.one_mul, neg_sub, Matrix.mul_sub,
        Matrix.mul_one]
    have := congrArg Matrix.det e
    rw [det_mul, det_mul, det_mul, hd, det_neg] at this
    refine mul_right_cancel₀ hP ?_
    linear_combination this

theorem kron_unit_sig {K G : Type} [Field K] [FunLike G K K] [RingHomClass G K K] (σ : G) {m n : ℕ}
    {a Gm : Matrix (Fin n) (Fin n) K} {b H : Matrix (Fin m) (Fin m) K} (hG : IsUnit Gm.det)
    (ha : (a.map σ)ᵀ * Gm * a = Gm) (hb : (b.map σ)ᵀ * H * b = H) :
    ((b ⊗ₖ aᵀ).map σ)ᵀ * (H ⊗ₖ Gm⁻¹ᵀ) * (b ⊗ₖ aᵀ) = H ⊗ₖ Gm⁻¹ᵀ := by
  have h1 : (Gm⁻¹ * (a.map σ)ᵀ * Gm) * a = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (a.map σ)ᵀ, ha, Matrix.nonsing_inv_mul _ hG]
  have h2 : a * Gm⁻¹ * (a.map σ)ᵀ = Gm⁻¹ := by
    have h3 := mul_eq_one_comm.1 h1
    calc a * Gm⁻¹ * (a.map σ)ᵀ = a * (Gm⁻¹ * (a.map σ)ᵀ * Gm) * Gm⁻¹ := by
          simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.mul_one]
      _ = Gm⁻¹ := by rw [h3, Matrix.one_mul]
  have e : ((b ⊗ₖ aᵀ).map σ)ᵀ = (b.map σ)ᵀ ⊗ₖ a.map σ := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp [Matrix.kroneckerMap_apply, map_mul]
  rw [e, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hb]
  congr 1
  conv_rhs => rw [← h2]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

theorem cart_exists {k : ℕ} (G : Matrix (Fin k) (Fin k) ℂ) (hG : Gᴴ = G) (hd : G.det ≠ 0) (r : ℝ) (hr : r ≠ 0) :
    ∃ s, Formalism.IndefR.Datum.IsCartanInv ((r : ℂ) • G) s := by
  refine GlobalTheory.Mem.ThetaNonzero.exists_isCartanInv ?_ (isUnit_iff_ne_zero.2 ?_)
  · show ((r : ℂ) • G)ᴴ = (r : ℂ) • G
    rw [conjTranspose_smul, hG, Complex.star_def, Complex.conj_ofReal]
  · rw [det_smul]
    exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.2 hr)) hd

theorem cart_refl {k : ℕ} (G : Matrix (Fin k) (Fin k) ℂ) (hG : Gᴴ = G) (hd : G.det ≠ 0) (r : ℝ) (hr : r ≠ 0)
    (y : Fin k → ℂ) (hy : star y ⬝ᵥ G *ᵥ y ≠ 0) (d : ℂ) :
    ∃ s, Formalism.IndefR.Datum.IsCartanInv ((r : ℂ) • G) s ∧
      s * (1 + d • vecMulVec y (star y ᵥ* G)) = (1 + d • vecMulVec y (star y ᵥ* G)) * s := by
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr
  obtain ⟨s, h1, h2⟩ := GlobalTheory.T.exists_cartanInvolution_comm_quasiReflection _ ((r : ℂ) • G)
    (by rw [conjTranspose_smul, hG, Complex.star_def, Complex.conj_ofReal])
    (by rw [det_smul]; exact mul_ne_zero (pow_ne_zero _ hr') hd) y
    (by
      have e : star y ⬝ᵥ ((r : ℂ) • G) *ᵥ y = (r : ℂ) * (star y ⬝ᵥ G *ᵥ y) := by
        simp only [dotProduct, mulVec, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      rw [e]
      exact mul_ne_zero hr' hy)
  refine ⟨s, h1, ?_⟩
  have e : d • vecMulVec y (star y ᵥ* G) = (d / r) • vecMulVec y (star y ᵥ* ((r : ℂ) • G)) := by
    ext i j
    simp only [Matrix.smul_apply, vecMulVec_apply, vecMul, dotProduct, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    field_simp
  rw [e]
  exact h2 _

theorem blk_comm {O : Type} [Fintype O] [DecidableEq O] {m n : ℕ} {sT b : O → Matrix (Fin m) (Fin m) ℂ}
    {sS a : O → Matrix (Fin n) (Fin n) ℂ} (h1 : ∀ w, sT w * b w = b w * sT w) (h2 : ∀ w, a w * sS w = sS w * a w) :
    GlobalTheory.RealWeil.blk sT sS * GlobalTheory.RealWeil.blk b a = GlobalTheory.RealWeil.blk b a * GlobalTheory.RealWeil.blk sT sS := by
  rw [GlobalTheory.RealWeil.blk_mul, GlobalTheory.RealWeil.blk_mul]
  congr 1 <;> funext w
  exacts [h1 w, h2 w]

end Abstract

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incAF_injective : Function.Injective (incAF F E) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)

theorem mt_unitary (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : GAF σ J) :
    ((mtF σ J g).map (cAF σ))ᵀ * J.map (incAF F E) * mtF σ J g = J.map (incAF F E) := g.2

theorem mt_ext {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g h : GAF σ J} (e : mtF σ J g = mtF σ J h) :
    g = h := Subtype.ext (Units.ext e)

theorem mt_one (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : mtF σ J 1 = 1 := rfl

theorem mt_mul (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g h : GAF σ J) :
    mtF σ J (g * h) = mtF σ J g * mtF σ J h := rfl

theorem map_unitary (σ : E →ₐ[F] E) {n : ℕ} (J a : Matrix (Fin n) (Fin n) E) :
    ((a.map (incAF F E)).map (cAF σ))ᵀ * J.map (incAF F E) * a.map (incAF F E) =
      ((a.map σ)ᵀ * J * a).map (incAF F E) := by
  rw [Matrix.map_mul, Matrix.map_mul]
  rfl

theorem det_ne_of_unitary {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J)
    {a : Matrix (Fin n) (Fin n) E} (h : (a.map σ)ᵀ * J * a = J) : a.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det h
  rw [det_mul, det_mul, h0, mul_zero] at this
  exact hJ.2 this.symm

theorem infPart_incAF (x : E) : infPartF F E (incAF F E x) = (1 : Ainf F) ⊗ₜ[F] x := by
  show Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] x) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem herm_map {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J)
    (τ : E →+* ℂ) : (J.map τ)ᴴ = J.map τ := by
  ext i j
  rw [conjTranspose_apply, Matrix.map_apply, Matrix.map_apply, ← hcm.2.2.2, hJ.1]

theorem det_map_ne {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) (τ : E →+* ℂ) :
    (J.map τ).det ≠ 0 := by
  rw [show (J.map τ).det = τ J.det from (RingHom.map_det τ J).symm]
  exact (map_ne_zero τ).2 hJ.2

theorem im_ne {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {ξ₀ : E} (h0 : ξ₀ ≠ 0) (hξ : σ ξ₀ = -ξ₀) (τ : E →+* ℂ) :
    (τ ξ₀).im ≠ 0 := by
  intro him
  have h1 : star (τ ξ₀) = -τ ξ₀ := by rw [← hcm.2.2.2, hξ, map_neg]
  have hre : (τ ξ₀).re = 0 := by
    have := congrArg Complex.re h1
    rw [Complex.star_def, Complex.conj_re, Complex.neg_re] at this
    linarith
  apply h0
  apply τ.injective
  rw [map_zero]
  exact Complex.ext (by rw [hre, Complex.zero_re]) (by rw [him, Complex.zero_im])

theorem hermE_alt (c : E ≃ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    GlobalTheory.UnRep.hermE c Jᵀ x y = (fun b => c (y b)) ⬝ᵥ J *ᵥ x := by
  simp only [GlobalTheory.UnRep.hermE, dotProduct, mulVec, transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem isUnE_iff (c : E ≃ₐ[F] E) {n : ℕ} (J M : Matrix (Fin n) (Fin n) E) :
    GlobalTheory.UnRep.IsUnE c Jᵀ M ↔ (M.map (c : E →ₐ[F] E))ᵀ * J * M = J := by
  have e1 : ∀ y : Fin n → E, (fun b => c ((M *ᵥ y) b)) = (fun b => c (y b)) ᵥ* (M.map (c : E →ₐ[F] E))ᵀ :=
    fun y => by
      rw [vecMul_transpose]
      funext i
      exact RingHom.map_mulVec ((c : E →ₐ[F] E) : E →+* E) M y i
  have e : ∀ x y, GlobalTheory.UnRep.hermE c Jᵀ (M *ᵥ x) (M *ᵥ y) =
      (fun b => c (y b)) ⬝ᵥ ((M.map (c : E →ₐ[F] E))ᵀ * J * M) *ᵥ x := fun x y => by
    rw [hermE_alt, e1, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have hs : ∀ i : Fin n, (fun b => c ((Pi.single i (1 : E) : Fin n → E) b)) = (Pi.single i (1 : E) : Fin n → E) :=
    fun i => funext fun b => by by_cases h : b = i <;> simp [h]
  refine ⟨fun h => ?_, fun h x y => by rw [e, h, hermE_alt]⟩
  ext i j
  have := h (Pi.single j 1) (Pi.single i 1)
  rw [e, hermE_alt, hs] at this
  simpa using this

theorem quad_map {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (c : E ≃ₐ[F] E) (hc : (c : E →ₐ[F] E) = σ) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (τ : E →+* ℂ) :
    star (τ ∘ x) ⬝ᵥ J.map τ *ᵥ (τ ∘ x) = τ (GlobalTheory.UnRep.hermE c Jᵀ x x) := by
  have h' : ∀ z, τ (c z) = star (τ z) := fun z => by rw [← hcm.2.2.2, ← hc]; rfl
  rw [hermE_alt, RingHom.map_dotProduct]
  congr 1
  · funext i
    simp [h']
  · funext i
    exact (RingHom.map_mulVec τ J x i).symm

theorem refl_map {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (c : E ≃ₐ[F] E) (hc : (c : E →ₐ[F] E) = σ) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (u : E) (τ : E →+* ℂ) :
    (GlobalTheory.UnRep.refl c Jᵀ x u).map τ =
      1 + τ ((u - 1) / GlobalTheory.UnRep.hermE c Jᵀ x x) • vecMulVec (τ ∘ x) (star (τ ∘ x) ᵥ* J.map τ) := by
  have h' : ∀ z, τ (c z) = star (τ z) := fun z => by rw [← hcm.2.2.2, ← hc]; rfl
  have e : τ ∘ (Jᵀ *ᵥ fun b => c (x b)) = star (τ ∘ x) ᵥ* J.map τ := by
    funext j
    simp only [Function.comp_apply, mulVec, vecMul, dotProduct, transpose_apply, map_sum, map_mul, Matrix.map_apply,
      Pi.star_apply, h']
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [GlobalTheory.UnRep.refl, ← RingHom.mapMatrix_apply, map_add, map_one, ← e]
  congr 1
  ext i j
  simp [vecMulVec_apply, map_mul]

end PositivityTheory.ThKW.GenA

end
