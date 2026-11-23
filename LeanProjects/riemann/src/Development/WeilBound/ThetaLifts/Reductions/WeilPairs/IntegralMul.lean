import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DCdE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdelicGLMulVecHaarEqModulusDetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatricesDiscreteCocompactAdelicMatrixSpaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHalfAbstract
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant
open scoped TensorProduct Matrix Kronecker
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.PhaseFourierInjectivity

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {nS nT : ℕ}

theorem hOF_eq_trace {m : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (J : Matrix (Fin m) (Fin m) E) (x y : WOF F E nS m) :
    hOF σ JS J x y = (JS⁻¹.map (incAF F E) * ((y.map (cAF σ))ᵀ * J.map (incAF F E) * x)).trace := by
  simp only [hOF, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem dC_dual (J : Matrix (Fin nT) (Fin nT) E) (hJ : J.det ≠ 0) :
    (dC E nT)ᵀ * GlobalTheory.WeilSchrodinger.DblTargetF.dblG J * dCdE J = 1 := by
  have e : GlobalTheory.WeilSchrodinger.DblTargetF.dblG J = (dbl J).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := rfl
  rw [e, dCdE, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id,
    diagCols, dbl, Matrix.transpose_fromRows, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
  simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_zero, add_zero, zero_add, neg_mul_neg, Matrix.neg_mul,
    Matrix.mul_neg, neg_neg, Matrix.mul_smul, Matrix.mul_nonsing_inv _ (Ne.isUnit hJ), ← add_smul]
  norm_num

theorem dC_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ) : (dC R n).map φ = dC S n := by
  ext i j
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective i
  simp only [dC, diagCols, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
  rcases k with k | k <;> simp [Matrix.one_apply, apply_ite φ]

theorem hOF_dual (JS : Matrix (Fin nS) (Fin nS) E) (J : Matrix (Fin nT) (Fin nT) E) (hJ : J.det ≠ 0) (v y : WOF F E nS nT) :
    hOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) (dCd F J * v) (dC (AF F ⊗[F] E) nT * y) =
      (JS⁻¹.map (incAF F E) * ((y.map (cAF σ))ᵀ * v)).trace := by
  have h := congrArg (fun M : Matrix (Fin nT) (Fin nT) E => M.map (incAF F E)) (dC_dual J hJ)
  simp only [Matrix.map_mul, Matrix.transpose_map, dC_map] at h
  rw [Matrix.map_one _ (map_zero _) (map_one _)] at h
  rw [hOF_eq_trace, Matrix.map_mul, dC_map, Matrix.transpose_mul]
  congr 2
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (dCd F J), ← Matrix.mul_assoc (dC _ nT)ᵀ, ← Matrix.mul_assoc (dC _ nT)ᵀ]
  rw [show (dC (AF F ⊗[F] E) nT)ᵀ * (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J).map (incAF F E) * dCd F J = 1 from h,
    Matrix.one_mul]

theorem phase_move (JS : Matrix (Fin nS) (Fin nS) E) (J : Matrix (Fin nT) (Fin nT) E) (hJ : J.det ≠ 0) (ξ₀ : E)
    (ψ : AddChar (AF F) ℂ) (s : GL (Fin nT) (AF F ⊗[F] E)) (y w : WOF F E nS nT) :
    phase σ JS J ξ₀ ψ ((s⁻¹).1 * y) ((s.1.map (cAF σ))ᵀ * w) = phase σ JS J ξ₀ ψ y w := by
  unfold phase symplOF
  rw [hOF_dual JS J hJ, hOF_dual JS J hJ, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc _ (s.1.map (cAF σ))ᵀ, ← Matrix.transpose_mul, ← Matrix.map_mul, Units.mul_inv,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul]

variable (F E nS nT) in

def vecE : WOF F E nS nT ≃+ (Fin (nT * nS) → AF F ⊗[F] E) where
  toFun w k := w (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  invFun u i j := u (finProdFinEquiv (i, j))
  left_inv w := by ext i j; simp only [Equiv.symm_apply_apply]
  right_inv u := by ext k; simp only [Prod.mk.eta, Equiv.apply_symm_apply]
  map_add' _ _ := rfl

theorem integral_mul (ν : Measure (WOF F E nS nT)) (hν : ν.IsAddHaarMeasure) (A : GL (Fin nT) (AF F ⊗[F] E))
    (g : WOF F E nS nT → ℂ) : ∫ w, g (A.1 * w) ∂ν =
      ((((distribHaarChar (AF F) (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
        (Matrix.GeneralLinearGroup.det A)) : ℝ) ^ nS)⁻¹ : ℝ) : ℂ) * ∫ w, g w ∂ν := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace F E nS nT
  have := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  letI : MeasurableSpace (Fin (nT * nS) → AF F ⊗[F] E) := borel _
  have : BorelSpace (Fin (nT * nS) → AF F ⊗[F] E) := ⟨rfl⟩
  have c1 : Continuous (vecE F E nS nT) :=
    continuous_pi fun k => (continuous_apply (finProdFinEquiv.symm k).2).comp (continuous_apply (finProdFinEquiv.symm k).1)
  have c2 : Continuous (vecE F E nS nT).symm := continuous_pi fun i => continuous_pi fun j => continuous_apply _
  let eh : WOF F E nS nT ≃ₜ (Fin (nT * nS) → AF F ⊗[F] E) := .mk (vecE F E nS nT).toEquiv c1 c2
  let em := eh.toMeasurableEquiv
  let K : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E) → Matrix (Fin (nT * nS)) (Fin (nT * nS)) (AF F ⊗[F] E) :=
    fun M => (M ⊗ₖ (1 : Matrix (Fin nS) (Fin nS) (AF F ⊗[F] E))).submatrix finProdFinEquiv.symm finProdFinEquiv.symm
  have hK : ∀ M M', M * M' = 1 → K M * K M' = 1 := fun M M' h => by
    simp only [K]
    rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul, h, Matrix.mul_one, Matrix.one_kronecker_one,
      Matrix.submatrix_one_equiv]
  let t : GL (Fin (nT * nS)) (AF F ⊗[F] E) := ⟨K A.1, K (A⁻¹).1, hK _ _ A.mul_inv, hK _ _ A.inv_mul⟩
  have hd : Matrix.GeneralLinearGroup.det t = Matrix.GeneralLinearGroup.det A ^ nS := by
    ext
    rw [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
    show (K A.1).det = _
    simp only [K]
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_kronecker, Matrix.det_one, one_pow, mul_one, Fintype.card_fin]
  have hv : ∀ w : WOF F E nS nT, (vecE F E nS nT).symm (t.1 *ᵥ vecE F E nS nT w) = A.1 * w := fun w => by
    ext i j
    show ∑ k, K A.1 (finProdFinEquiv (i, j)) k * vecE F E nS nT w k = ∑ k, A.1 i k * w k j
    rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    show ∑ b, K A.1 (finProdFinEquiv (i, j)) (finProdFinEquiv (a, b)) *
      w (finProdFinEquiv.symm (finProdFinEquiv (a, b))).1 (finProdFinEquiv.symm (finProdFinEquiv (a, b))).2 = _
    simp only [K, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]
    simp
  have h := GlobalTheory.T.integral_adelicGL_mulVec_haar_eq_modulus_det F E _ t (ν.map em) ((vecE F E nS nT).isAddHaarMeasure_map ν c1 c2)
    (fun u => g ((vecE F E nS nT).symm u))
  rw [integral_map_equiv, integral_map_equiv, hd, map_pow, map_pow, NNReal.coe_pow] at h
  refine Eq.trans ?_ (h.trans ?_)
  · congr 1
    funext w
    exact congrArg g (hv w).symm
  · congr 2
    funext w
    exact congrArg g ((vecE F E nS nT).symm_apply_apply w)

end

theorem change : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
    ∀ (s : GL (Fin nT) (AF F ⊗[F] E)) (N : WOF F E nS nT → ℂ), Continuous N → Integrable N ν →
      Continuous (fun w : WOF F E nS nT => N ((s.1.map (cAF σ))ᵀ * w)) ∧
      Integrable (fun w : WOF F E nS nT => N ((s.1.map (cAF σ))ᵀ * w)) ν ∧
      ∀ y : WOF F E nS nT, ∫ v, phase σ JS JT ξ₀ B.ψ ((s⁻¹).1 * y) v * N v ∂ν =
        ((mfac F E nS s : ℝ) : ℂ) ^ 2 * ∫ w, phase σ JS JT ξ₀ B.ψ y w * N ((s.1.map (cAF σ))ᵀ * w) ∂ν := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσ ν 𝓕 hν h𝓕 s N hN hI
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace F E nS nT
  have := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  have hA : ∀ M M' : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E), M * M' = 1 → (M'.map (cAF σ))ᵀ * (M.map (cAF σ))ᵀ = 1 :=
    fun M M' h => by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  let A : GL (Fin nT) (AF F ⊗[F] E) := ⟨(s.1.map (cAF σ))ᵀ, ((s⁻¹).1.map (cAF σ))ᵀ, hA _ _ s.inv_mul, hA _ _ s.mul_inv⟩
  let e : WOF F E nS nT ≃+ WOF F E nS nT :=
    { toFun := fun w => A.1 * w
      invFun := fun w => (A⁻¹).1 * w
      left_inv := fun w => by simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      right_inv := fun w => by simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      map_add' := fun v w => Matrix.mul_add _ v w }
  have c1 : Continuous e := continuous_const.matrix_mul continuous_id
  have c2 : Continuous e.symm := continuous_const.matrix_mul continuous_id
  refine ⟨hN.comp c1, ?_, fun y => ?_⟩
  · have : (ν.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map ν c1 c2
    obtain ⟨c, hc⟩ : ∃ c : NNReal, ν.map e = c • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul _ ν⟩
    have h1 : Integrable N (ν.map e) := by
      rw [hc]
      exact hI.smul_measure_nnreal
    exact (integrable_map_measure hN.aestronglyMeasurable c1.measurable.aemeasurable).1 h1
  · have h := integral_mul ν hν A (fun v => phase σ JS JT ξ₀ B.ψ ((s⁻¹).1 * y) v * N v)
    have hn : Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det A) =
        Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det s) := by
      refine Units.ext (GlobalTheory.SplitDetCharF.tensor_inj (F := F) (E := E) ?_)
      have hcc : ∀ z : AF F ⊗[F] E, cAF σ (cAF σ z) = z := fun z => by
        induction z using TensorProduct.induction_on with
        | zero => rw [map_zero, map_zero]
        | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (GlobalTheory.SplitDetCharF.sig_invol hB.cm x)
        | add x y hx hy => rw [map_add, map_add, hx, hy]
      have hd : A.1.det = cAF σ s.1.det := by
        show ((s.1.map (cAF σ))ᵀ).det = _
        rw [Matrix.det_transpose, RingHom.map_det]; rfl
      show algebraMap _ _ (Algebra.norm (AF F) A.1.det) = algebraMap _ _ (Algebra.norm (AF F) s.1.det)
      rw [GlobalTheory.SplitDetCharF.algebraMap_norm hB.cm, GlobalTheory.SplitDetCharF.algebraMap_norm hB.cm, hd, hcc, mul_comm]
    rw [hn] at h
    set m : ℝ := (distribHaarChar (AF F) (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
      (Matrix.GeneralLinearGroup.det s)) : ℝ) with hm
    have hm0 : 0 < m := NNReal.coe_pos.2 distribHaarChar_pos
    have hf : mfac F E nS s ^ 2 = m ^ nS := by
      show (m ^ ((Fintype.card (Fin nS) : ℝ) / 2)) ^ 2 = _
      rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le, Fintype.card_fin, ← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    have h2 : (fun w : WOF F E nS nT => phase σ JS JT ξ₀ B.ψ ((s⁻¹).1 * y) (A.1 * w) * N (A.1 * w)) =
        fun w => phase σ JS JT ξ₀ B.ψ y w * N ((s.1.map (cAF σ))ᵀ * w) := funext fun w => by
      rw [← phase_move JS JT hT.2 ξ₀ B.ψ s y w]
    rw [h2] at h
    rw [h, ← Complex.ofReal_pow, hf, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (pow_pos hm0 _).ne',
      Complex.ofReal_one, one_mul]

end PositivityTheory.ThKW.PhaseFourierInjectivity

end
