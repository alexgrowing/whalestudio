import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount

open Formalism.FourierDecayAlt Matrix
open scoped ComplexConjugate InnerProductSpace ComplexOrder

namespace Formalism.FourierDecayAlt.P

theorem torus_action_group : C7.TaGroup := by
  intro a b φ ψ
  refine ⟨?_, ?_, ?_⟩
  · unfold C7.taS; rw [Complex.norm_exp]; simp
  · unfold C7.taS; rw [← Complex.exp_add]; congr 1; push_cast; ring
  · simp [C7.taS]

theorem torus_argument_multiplicative : C7.TaArgMul := by
  intro a b Dr ζ hDr hζ
  have h := Complex.arg_mul_coe_angle hDr hζ
  rw [← Real.Angle.coe_add, Real.Angle.angle_eq_iff_two_pi_dvd_sub] at h
  obtain ⟨m, hm⟩ := h
  have e : Complex.arg (Dr * ζ) = Complex.arg Dr + Complex.arg ζ + 2 * Real.pi * m := by linarith
  unfold C7.taS
  rw [← Complex.exp_add, e, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-(m * (a + b)), ?_⟩
  push_cast; ring

theorem hilbertSchmidt_frame : C7.HSFrame := by
  intro E E' _ _ _ _ _ _ U U' J₁ J₂
  have hadj : ∀ J : E' →L[ℂ] E, ContinuousLinearMap.adjoint (C7.frameConj U U' J) =
      (U'.symm.toContinuousLinearEquiv : E' →L[ℂ] E') ∘L ContinuousLinearMap.adjoint J ∘L
        (U.toContinuousLinearEquiv : E →L[ℂ] E) := by
    intro J
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    simp only [C7.frameConj, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rw [← U'.inner_map_map, LinearIsometryEquiv.apply_symm_apply, ContinuousLinearMap.adjoint_inner_left,
      ← U.inner_map_map (x := x), LinearIsometryEquiv.apply_symm_apply]
  have e : ((ContinuousLinearMap.adjoint (C7.frameConj U U' J₂) ∘L C7.frameConj U U' J₁ : E' →L[ℂ] E') :
      E' →ₗ[ℂ] E') = (U'.symm.toLinearEquiv).conj
        ((ContinuousLinearMap.adjoint J₂ ∘L J₁ : E' →L[ℂ] E') : E' →ₗ[ℂ] E') := by
    apply LinearMap.ext; intro x
    rw [hadj]
    simp [C7.frameConj, LinearEquiv.conj_apply]
  rw [e, LinearMap.trace_conj']

theorem schur_product_posSemidef : C7.SchurProductPSD := by
  intro ι _ _ A C hA hC
  exact hA.hadamard hC

theorem c7_form_mono : C7.FormMono := by
  intro ι _ _ H _ _ V K K' hA
  have hG : ((Matrix.gram ℂ V)ᵀ).PosSemidef := (Matrix.posSemidef_gram (𝕜 := ℂ) V).transpose
  have hM := hA.hadamard hG
  have := hM.dotProduct_mulVec_nonneg (fun _ => (1 : ℂ))
  simpa [dotProduct, mulVec, Matrix.hadamard_apply, Matrix.gram_apply, Matrix.transpose_apply] using this

theorem c7_form_mono_of_schur : C7.FormMonoOfSchur := fun _ => c7_form_mono

theorem extend_by_zero_posSemidef : C7.ExtendZeroPSD := by
  intro ι _ _ S _ K hK
  classical
  let P : Matrix S ι ℂ := Matrix.of fun s w => if (s : ι) = w then 1 else 0
  convert hK.conjTranspose_mul_mul_same P using 1
  ext w w'
  simp only [P, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases hw : w ∈ S <;> by_cases hw' : w' ∈ S
  · rw [dif_pos ⟨hw, hw'⟩]
    rw [Finset.sum_eq_single ⟨w', hw'⟩]
    · rw [Finset.sum_eq_single ⟨w, hw⟩]
      · simp
      · intro s _ hs; have : (s : ι) ≠ w := fun h => hs (Subtype.ext h); simp [this]
      · simp
    · intro s _ hs; have : (s : ι) ≠ w' := fun h => hs (Subtype.ext h); simp [this]
    · simp
  all_goals
    rw [dif_neg (by tauto)]
    symm
    apply Finset.sum_eq_zero
    intro s _
  · have : (s : ι) ≠ w' := fun h => hw' (h ▸ s.2); simp [this]
  · have : ∀ t : S, (t : ι) ≠ w := fun t h => hw (h ▸ t.2); simp [this]
  · have : ∀ t : S, (t : ι) ≠ w := fun t h => hw (h ▸ t.2); simp [this]

theorem schur_isotypic_decomposition : C7.SchurIsotypic := by
  intro K _ E E' R _ _ _ _ _ _ _ _ _ π π' ρ hπ hπ' _ hno J hJ φ hφ v x
  have unit : ∀ {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] (σ : K →* (A →L[ℂ] A)),
      C7.IsUnitaryRep σ → ∀ k a b, ⟪σ k a, b⟫_ℂ = ⟪a, σ k⁻¹ b⟫_ℂ := by
    intro A _ _ σ hσ k a b
    have e : σ k (σ k⁻¹ b) = b := by
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]
    conv_lhs => rw [← e]
    exact hσ k a (σ k⁻¹ b)
  let ψ : R →L[ℂ] E' := ContinuousLinearMap.adjoint J ∘L φ
  have hψ : C7.Intertw ρ π' ψ := by
    intro k
    ext y
    apply ext_inner_right ℂ
    intro z
    simp only [ψ, ContinuousLinearMap.comp_apply]
    rw [unit π' hπ', ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
    have h1 := DFunLike.congr_fun (hJ k⁻¹) z
    have h2 := DFunLike.congr_fun (hφ k) y
    simp only [ContinuousLinearMap.comp_apply] at h1 h2
    rw [← h1, ← unit π hπ, h2]
  have h0 := hno ψ hψ
  have : ⟪φ x, J v⟫_ℂ = ⟪ψ x, v⟫_ℂ := by
    simp only [ψ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
  rw [this, h0]; simp

end Formalism.FourierDecayAlt.P
