import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountUpSt

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.ChowHt GlobalTheory.HermTools

namespace GlobalTheory.HilbertSamuel

theorem denseRange_of_not_isReal {K : Type*} [Field K] {σ : K →+* ℂ} (hσ : ¬ComplexEmbedding.IsReal σ) :
    DenseRange σ := by
  rcases Complex.subfield_eq_of_closed (Subfield.isClosed_topologicalClosure σ.fieldRange) with h | h
  · refine absurd (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)) hσ
    obtain ⟨r, hr⟩ := h.le (Subfield.le_topologicalClosure _ ⟨x, rfl⟩)
    rw [ComplexEmbedding.conjugate_coe_eq, ← hr]
    exact Complex.conj_ofReal r
  · rw [denseRange_iff_closure_range, ← RingHom.coe_fieldRange]
    exact congrArg (fun s : Subfield ℂ => (s : Set ℂ)) h

theorem frameNorm_mul {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (c : ℂ) (x : Fin N → ℂ) :
    frameNorm A (fun j => c * x j) = ‖c‖ * frameNorm A x := by
  change frameNorm A (c • x) = _
  simp only [frameNorm, Matrix.mulVec_smul, Pi.smul_apply, norm_smul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem continuous_frameNorm {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) : Continuous (frameNorm A) := by
  unfold frameNorm Matrix.mulVec dotProduct
  fun_prop

theorem continuous_cnrm {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι] (h : HermFam K V)
    (σ : K →+* ℂ) (v : ι → V) : Continuous fun c => cnrm h σ c v := by
  unfold cnrm csq
  fun_prop

variable {F : Type} [Field F] [NumberField F]

theorem exists_smul_mem_span {V : Type*} [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V]
    {S : Set V} (hS : Submodule.span F S = ⊤) (x : V) : ∃ a : F, a ≠ 0 ∧ a • x ∈ Submodule.span (𝓞 F) S := by
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 F)) F S x (hS.ge trivial)
  refine ⟨algebraMap (𝓞 F) F t, ?_, by rwa [algebraMap_smul]⟩
  exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2 (nonZeroDivisors.coe_ne_zero t)

namespace Data

variable {X : Data F} {β : (F →+* ℂ) → ℝ}

theorem MulBound.of_field (h : X.MulBound β) {j : ℕ} (hj : j < X.T) (σ : F →+* ℂ) (u : Fin X.N → F) (f : X.V j)
    (g : X.V (j + 1)) (e : (g : X.Sec (j + 1)) = X.mulW j u f) :
    (X.nm (j + 1)).nrm σ g ≤ Real.sqrt (β σ) * frameNorm (X.A σ) (fun k => σ (u k)) * (X.nm j).nrm σ f := by
  obtain ⟨a, ha, hu⟩ := exists_smul_mem_span X.geom.alg.spans u
  obtain ⟨b, hb, hf⟩ := exists_smul_mem_span (X.full j).span f
  rw [Submodule.span_eq] at hf
  have key : (X.nm (j + 1)).nrm σ (a • b • g) ≤
      Real.sqrt (β σ) * frameNorm (X.A σ) (fun k => σ (a * u k)) * (X.nm j).nrm σ (b • f) :=
    h j hj σ _ hu _ hf (a • b • g) (by
      rw [Submodule.coe_smul, Submodule.coe_smul, Submodule.coe_smul, e, map_smul, map_smul, LinearMap.smul_apply,
        smul_comm])
  simp only [map_mul, frameNorm_mul, HermFam.nrm_smul_up] at key
  have ha' : 0 < ‖σ a‖ := norm_pos_iff.2 ((map_ne_zero σ).2 ha)
  have hb' : 0 < ‖σ b‖ := norm_pos_iff.2 ((map_ne_zero σ).2 hb)
  exact le_of_mul_le_mul_left (by linarith) (mul_pos ha' hb')

theorem MulBound.mulBoundAt_of_not_isReal (h : X.MulBound β) {σ : F →+* ℂ} (hσ : ¬ComplexEmbedding.IsReal σ) :
    X.MulBoundAt σ (β σ) := fun j hj u m c f g hg => by
  have hd := denseRange_of_not_isReal hσ
  refine ((DenseRange.piMap fun _ : Fin X.N => hd).prodMap (DenseRange.piMap fun _ : Fin m => hd)).induction_on
    (p := fun z => cnrm (X.nm (j + 1)) σ (fun t => z.1 t.1 * z.2 t.2) g ≤
      Real.sqrt (β σ) * frameNorm (X.A σ) z.1 * cnrm (X.nm j) σ z.2 f) (u, c) ?_ ?_
  · exact isClosed_le ((continuous_cnrm _ _ _).comp (by fun_prop))
      ((continuous_const.mul ((continuous_frameNorm _).comp continuous_fst)).mul
        ((continuous_cnrm _ _ _).comp continuous_snd))
  · rintro ⟨a, b⟩
    have := h.of_field hj σ a (∑ i, b i • f i) (∑ t : Fin X.N × Fin m, (a t.1 * b t.2) • g t) (by
      conv_rhs => rw [pi_eq_sum_univ' a]
      simp only [Fintype.sum_prod_type, Submodule.coe_sum, Submodule.coe_smul, hg, map_sum, map_smul,
        LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, mul_smul]
      exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => smul_comm _ _ _))
    simp only [← cnrm_map, map_mul] at this
    exact this

theorem MulBound.mulBoundAt [IsTotallyComplex F] (h : X.MulBound β) (σ : F →+* ℂ) : X.MulBoundAt σ (β σ) :=
  h.mulBoundAt_of_not_isReal (IsTotallyComplex.complexEmbedding_not_isReal σ)

end Data

end GlobalTheory.HilbertSamuel
