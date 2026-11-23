import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothA

noncomputable section

open Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

private theorem Jm_mul_selfDiscreteSeriesExistence (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

private theorem Jm_conjTransposeDiscreteSeriesExistence (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  simp only [Pi.star_apply]
  split_ifs <;> simp

private theorem Jm_mul_Jm_mul_eq (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) :
    Jm ε * (Jm ε * Y) = Y := by
  rw [← Matrix.mul_assoc, Jm_mul_selfDiscreteSeriesExistence, Matrix.one_mul]

theorem inv_eq_signature_conjTranspose_conj {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    g⁻¹ = Jm ε * gᴴ * Jm ε := by
  have h : gᴴ * Jm ε * g = Jm ε := hg
  apply Matrix.inv_eq_left_inv
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h, Jm_mul_selfDiscreteSeriesExistence]

theorem inv_mul_self_of_mem_indefiniteUnitary {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    g⁻¹ * g = 1 := by
  have h : gᴴ * Jm ε * g = Jm ε := hg
  rw [inv_eq_signature_conjTranspose_conj hg, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h, Jm_mul_selfDiscreteSeriesExistence]

theorem mul_inv_self_of_mem_indefiniteUnitary {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse (inv_mul_self_of_mem_indefiniteUnitary hg))

theorem isUnit_of_mem_indefiniteUnitary {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) : IsUnit g :=
  ⟨⟨g, g⁻¹, mul_inv_self_of_mem_indefiniteUnitary hg, inv_mul_self_of_mem_indefiniteUnitary hg⟩, rfl⟩

theorem inG_conj_unitary {ε : Fin n → Bool} {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε)
    (hX : inG ε X) : inG ε (g * X * g⁻¹) := by
  have hJ : Jm ε * Jm ε = 1 := Jm_mul_selfDiscreteSeriesExistence ε
  have hJh : (Jm ε)ᴴ = Jm ε := Jm_conjTransposeDiscreteSeriesExistence ε
  have hX0 : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  have hX' : Jm ε * Xᴴ + X * Jm ε = 0 := by
    have e : Jm ε * Xᴴ + X * Jm ε = Jm ε * (Xᴴ * Jm ε + Jm ε * X) * Jm ε := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hJ, Matrix.mul_one,
        Jm_mul_Jm_mul_eq]
    rw [e, hX0, Matrix.mul_zero, Matrix.zero_mul]
  have key : (g * X * g⁻¹)ᴴ * Jm ε + Jm ε * (g * X * g⁻¹) =
      Jm ε * g * (Jm ε * Xᴴ + X * Jm ε) * gᴴ * Jm ε := by
    rw [inv_eq_signature_conjTranspose_conj hg]
    simp only [Matrix.conjTranspose_mul, hJh, Matrix.conjTranspose_conjTranspose, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_assoc]
  show (g * X * g⁻¹)ᴴ * Jm ε + Jm ε * (g * X * g⁻¹) = 0
  rw [key, hX', Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul]

private theorem Jm_conjTranspose_Jm_eq_neg_of_inG {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    Jm ε * Xᴴ * Jm ε = -X := by
  have h0 : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  have h1 : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left h0
  rw [Matrix.mul_assoc, h1, Matrix.mul_neg, Jm_mul_Jm_mul_eq]

theorem conj_involution_complex_comb {ε : Fin n → Bool} {A B : Matrix (Fin n) (Fin n) ℂ} (hA : inG ε A) (hB : inG ε B) :
    stJ ε (A + Complex.I • B) = -A + Complex.I • B := by
  unfold stJ
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Jm_conjTranspose_Jm_eq_neg_of_inG hA, Jm_conjTranspose_Jm_eq_neg_of_inG hB]
  simp [Complex.star_def, Complex.conj_I]

theorem actM_add_smul {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (X Y : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    actM E (X + c • Y) = actM E X + c • actM E Y := by
  simp only [actM, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_smul, mul_smul,
    Finset.sum_add_distrib, Finset.smul_sum]

theorem actM_neg {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (X : Matrix (Fin n) (Fin n) ℂ) : actM E (-X) = -actM E X := by
  simp only [actM, Matrix.neg_apply, neg_smul, Finset.sum_neg_distrib]

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem isometry_inner_eq {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {h : Matrix (Fin n) (Fin n) ℂ}
    (hn : ∀ v : H, ‖σ h v‖ = ‖v‖) (a b : H) : ⟪σ h a, σ h b⟫_ℂ = ⟪a, b⟫_ℂ := by
  exact LinearIsometry.inner_map_map
    ({ toLinearMap := (σ h : H →ₗ[ℂ] H), norm_map' := hn } : H →ₗᵢ[ℂ] H) a b

theorem derived_action_skew_adjoint {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {w : H} (hw : w ∈ smD ε σ) {Y : Matrix (Fin n) (Fin n) ℂ}
    (hY : inG ε Y) {u u' : H}
    (hu : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • Y)) u) u' 0) :
    ⟪w, u'⟫_ℂ = -⟪((actM (smE ε σ) Y ⟨w, hw⟩ : smD ε σ) : H), u⟫_ℂ := by
  have hd := (isDerivedOn_smE hσ).deriv Y hY ⟨w, hw⟩
  have h3 : HasDerivAt
      (fun t : ℝ => ⟪σ (NormedSpace.exp ((t : ℂ) • Y)) w, σ (NormedSpace.exp ((t : ℂ) • Y)) u⟫_ℂ)
      (⟪σ (NormedSpace.exp (((0 : ℝ) : ℂ) • Y)) w, u'⟫_ℂ +
        ⟪((actM (smE ε σ) Y ⟨w, hw⟩ : smD ε σ) : H), σ (NormedSpace.exp (((0 : ℝ) : ℂ) • Y)) u⟫_ℂ) 0 :=
    hd.inner ℂ hu
  have h4 : (fun t : ℝ =>
      ⟪σ (NormedSpace.exp ((t : ℂ) • Y)) w, σ (NormedSpace.exp ((t : ℂ) • Y)) u⟫_ℂ) =
      fun _ => ⟪w, u⟫_ℂ :=
    funext fun t => isometry_inner_eq (hσ.2.1 _ (exp_smul_mem_UJset hY t)) w u
  rw [h4] at h3
  have h5 := h3.unique (hasDerivAt_const (0 : ℝ) ⟪w, u⟫_ℂ)
  have h0 : NormedSpace.exp (((0 : ℝ) : ℂ) • Y) = 1 := by simp
  rw [h0, hσ.1.1] at h5
  simp only [ContinuousLinearMap.one_apply] at h5
  exact eq_neg_of_add_eq_zero_left h5

theorem hasDerivAt_conj_exp_action {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {w : H} (hw : w ∈ smD ε σ) {g X : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) (hX : inG ε X) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹))) (σ g w))
      (σ g ((actM (smE ε σ) X ⟨w, hw⟩ : smD ε σ) : H)) 0 := by
  have hgX : inG ε (g * X * g⁻¹) := inG_conj_unitary hg hX
  have hd := (isDerivedOn_smE hσ).deriv X hX ⟨w, hw⟩
  have hfun : (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹))) (σ g w)) =
      fun t : ℝ => σ g (σ (NormedSpace.exp ((t : ℂ) • X)) w) := by
    funext t
    have hm : NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹)) * g = g * NormedSpace.exp ((t : ℂ) • X) := by
      rw [show (t : ℂ) • (g * X * g⁻¹) = g * ((t : ℂ) • X) * g⁻¹ by
          rw [Matrix.mul_smul, Matrix.smul_mul],
        Matrix.exp_conj g _ (isUnit_of_mem_indefiniteUnitary hg), Matrix.mul_assoc, inv_mul_self_of_mem_indefiniteUnitary hg, Matrix.mul_one]
    have h1 := hσ.1.2 _ (exp_smul_mem_UJset hgX t) g hg
    have h2 := hσ.1.2 g hg _ (exp_smul_mem_UJset hX t)
    rw [hm] at h1
    exact congrArg (fun L : H →L[ℂ] H => L w) (h1.symm.trans h2)
  rw [hfun]
  exact ((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd

end Rep

private theorem inG_of_Jm_conj_eq_neg {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ}
    (h : Jm ε * Yᴴ * Jm ε = -Y) : inG ε Y := by
  show Yᴴ * Jm ε + Jm ε * Y = 0
  have e : Yᴴ * Jm ε = Jm ε * (Jm ε * Yᴴ * Jm ε) := by
    rw [Matrix.mul_assoc (Jm ε) Yᴴ, Jm_mul_Jm_mul_eq]
  rw [e, h, Matrix.mul_neg, neg_add_cancel]

private theorem exists_inG_add_I_smul_inG (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    ∃ A B : Matrix (Fin n) (Fin n) ℂ, inG ε A ∧ inG ε B ∧ X = A + Complex.I • B := by
  have hJ : Jm ε * Jm ε = 1 := Jm_mul_selfDiscreteSeriesExistence ε
  have hJh : (Jm ε)ᴴ = Jm ε := Jm_conjTransposeDiscreteSeriesExistence ε
  refine ⟨(1 / 2 : ℂ) • (X - Jm ε * Xᴴ * Jm ε), (1 / (2 * Complex.I)) • (X + Jm ε * Xᴴ * Jm ε),
    ?_, ?_, ?_⟩
  · apply inG_of_Jm_conj_eq_neg
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hJh,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_assoc, hJ, Matrix.mul_one, Jm_mul_Jm_mul_eq]
    rw [show star (1 / 2 : ℂ) = 1 / 2 by simp, ← smul_neg, neg_sub]
  · apply inG_of_Jm_conj_eq_neg
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hJh,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_assoc, hJ, Matrix.mul_one, Jm_mul_Jm_mul_eq]
    have hc : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
      simp [Complex.star_def, Complex.conj_I]
    rw [hc, neg_smul, add_comm (Jm ε * (Xᴴ * Jm ε)) X]
  · have hI : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
      rw [mul_one_div, mul_comm 2 Complex.I, ← div_div, div_self Complex.I_ne_zero]
    have h2 : X - Jm ε * Xᴴ * Jm ε + (X + Jm ε * Xᴴ * Jm ε) = (2 : ℂ) • X := by
      rw [two_smul]; abel
    rw [smul_smul, hI, ← smul_add, h2, smul_smul]
    norm_num

theorem b3a : MatrixCoeffConjugationMove := by
  intro n ε H _ _ σ w hσ hw g hg X
  have hφ : ∀ Y, phiW ε σ w Y = ((actM (smE ε σ) Y ⟨w, hw⟩ : smD ε σ) : H) := fun Y => by
    simp only [phiW, dif_pos hw]
  have hlin : ∀ (Y Z : Matrix (Fin n) (Fin n) ℂ) (c : ℂ),
      ((actM (smE ε σ) (Y + c • Z) ⟨w, hw⟩ : smD ε σ) : H) =
        ((actM (smE ε σ) Y ⟨w, hw⟩ : smD ε σ) : H) +
          c • ((actM (smE ε σ) Z ⟨w, hw⟩ : smD ε σ) : H) := by
    intro Y Z c
    rw [actM_add_smul]
    simp
  have hneg : ∀ Y, ((actM (smE ε σ) (-Y) ⟨w, hw⟩ : smD ε σ) : H) =
      -((actM (smE ε σ) Y ⟨w, hw⟩ : smD ε σ) : H) := by
    intro Y
    rw [actM_neg]
    simp
  have key : ∀ Y, inG ε Y → ⟪w, σ g ((actM (smE ε σ) Y ⟨w, hw⟩ : smD ε σ) : H)⟫_ℂ =
      -⟪((actM (smE ε σ) (g * Y * g⁻¹) ⟨w, hw⟩ : smD ε σ) : H), σ g w⟫_ℂ :=
    fun Y hY => derived_action_skew_adjoint hσ hw (inG_conj_unitary hg hY) (hasDerivAt_conj_exp_action hσ hw hg hY)
  obtain ⟨A, B, hA, hB, rfl⟩ := exists_inG_add_I_smul_inG ε X
  have hconj : g * (A + Complex.I • B) * g⁻¹ = g * A * g⁻¹ + Complex.I • (g * B * g⁻¹) := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hconj, conj_involution_complex_comb (inG_conj_unitary hg hA) (inG_conj_unitary hg hB), hφ, hφ, hlin, hlin, hneg,
    map_add, map_smul, inner_add_right, inner_smul_right, inner_add_left, inner_smul_left,
    inner_neg_left, key A hA, key B hB]
  simp only [Complex.conj_I]
  ring

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
