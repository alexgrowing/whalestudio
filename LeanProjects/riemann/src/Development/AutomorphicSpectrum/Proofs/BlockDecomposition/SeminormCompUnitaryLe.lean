import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.ComplexMatrixMajorantIntegrable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulCIff
open MeasureTheory Matrix
open Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.GodementFE

noncomputable section

namespace GlobalTheory.CompanionTheory.UnitaryCompSchwartz

def rowMul (A : Matrix (Fin 2) (Fin 2) ℂ) : (Fin 2 → ℂ) →L[ℝ] (Fin 2 → ℂ) :=
  { toFun := fun v => Matrix.vecMul v A
    map_add' := fun x y => Matrix.add_vecMul A x y
    map_smul' := fun r x => by simp [Matrix.smul_vecMul]
    cont := by
      refine LinearMap.continuous_of_finiteDimensional
        ({ toFun := fun v => Matrix.vecMul v A
           map_add' := fun x y => Matrix.add_vecMul A x y
           map_smul' := fun r x => by simp [Matrix.smul_vecMul] } :
          (Fin 2 → ℂ) →ₗ[ℝ] (Fin 2 → ℂ)) }

theorem rowMul_apply (A : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    rowMul A v = Matrix.vecMul v A := rfl

theorem entry_le_one {κ : Matrix (Fin 2) (Fin 2) ℂ} (h : κ * κᴴ = 1) (i j : Fin 2) :
    ‖κ i j‖ ≤ 1 := by
  have h1 := congrFun (congrFun h i) i
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
    Complex.star_def, Complex.mul_conj'] at h1
  have h2 : ‖κ i 0‖ ^ 2 + ‖κ i 1‖ ^ 2 = 1 := by exact_mod_cast h1
  fin_cases j
  · show ‖κ i 0‖ ≤ 1
    nlinarith [norm_nonneg (κ i 0), sq_nonneg (‖κ i 1‖)]
  · show ‖κ i 1‖ ≤ 1
    nlinarith [norm_nonneg (κ i 1), sq_nonneg (‖κ i 0‖)]

theorem norm_rowMul_le {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : ∀ i j, ‖A i j‖ ≤ 1) :
    ‖rowMul A‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun v => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  have h0 : ‖v 0‖ ≤ ‖v‖ := norm_le_pi_norm v 0
  have h1 : ‖v 1‖ ≤ ‖v‖ := norm_le_pi_norm v 1
  have e : rowMul A v j = v 0 * A 0 j + v 1 * A 1 j := by
    simp [rowMul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  rw [e]
  calc ‖v 0 * A 0 j + v 1 * A 1 j‖ ≤ ‖v 0‖ * ‖A 0 j‖ + ‖v 1‖ * ‖A 1 j‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
    _ ≤ ‖v‖ * 1 + ‖v‖ * 1 := by
        gcongr
        · exact hA 0 j
        · exact hA 1 j
    _ = 2 * ‖v‖ := by ring

theorem seminorm_comp_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L L' : E →L[ℝ] E) (hLL : ∀ z, L' (L z) = z) (hL : ‖L‖ ≤ 2) (hL' : ‖L'‖ ≤ 2)
    (f f' : SchwartzMap E ℂ) (hf : ∀ z, f' z = f (L z)) (i j : ℕ) :
    SchwartzMap.seminorm ℝ i j f' ≤ 2 ^ (i + j) * SchwartzMap.seminorm ℝ i j f := by
  refine SchwartzMap.seminorm_le_bound ℝ i j f' (by positivity) fun z => ?_
  have hcomp : (f' : E → ℂ) = (f : E → ℂ) ∘ L := funext hf
  have hz : ‖z‖ ≤ 2 * ‖L z‖ := by
    calc ‖z‖ = ‖L' (L z)‖ := by rw [hLL]
      _ ≤ ‖L'‖ * ‖L z‖ := L'.le_opNorm _
      _ ≤ 2 * ‖L z‖ := by gcongr
  have hD : ‖iteratedFDeriv ℝ j (f' : E → ℂ) z‖ ≤
      ‖iteratedFDeriv ℝ j (f : E → ℂ) (L z)‖ * 2 ^ j := by
    rw [hcomp, L.iteratedFDeriv_comp_right (f.smooth ⊤) z (by exact_mod_cast le_top)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    gcongr
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    gcongr
  calc ‖z‖ ^ i * ‖iteratedFDeriv ℝ j (f' : E → ℂ) z‖
      ≤ (2 * ‖L z‖) ^ i * (‖iteratedFDeriv ℝ j (f : E → ℂ) (L z)‖ * 2 ^ j) := by gcongr
    _ = 2 ^ (i + j) * (‖L z‖ ^ i * ‖iteratedFDeriv ℝ j (f : E → ℂ) (L z)‖) := by
        rw [mul_pow, pow_add]; ring
    _ ≤ 2 ^ (i + j) * SchwartzMap.seminorm ℝ i j f := by
        gcongr
        exact SchwartzMap.le_seminorm ℝ i j f (L z)

theorem comp_unitary_bounded : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ κ : Matrix (Fin 2) (Fin 2) ℂ, κ * κᴴ = 1 →
    ∀ f : SchwartzMap (Fin 2 → ℂ) ℂ, ∃ f' : SchwartzMap (Fin 2 → ℂ) ℂ,
      (∀ v, f' v = f (Matrix.vecMul v κ)) ∧ pS N f' ≤ C * pS N f := by
  intro N
  refine ⟨4 ^ N, by positivity, fun κ hκ f => ?_⟩
  have hκ' : κᴴ * κ = 1 := mul_eq_one_comm.1 hκ
  have hb : ∀ i j, ‖κ i j‖ ≤ 1 := entry_le_one hκ
  have hb' : ∀ i j, ‖κᴴ i j‖ ≤ 1 := fun i j => by
    rw [Matrix.conjTranspose_apply, norm_star]
    exact hb j i
  have h12 : ∀ z, rowMul κᴴ (rowMul κ z) = z := fun z => by
    simp [rowMul_apply, Matrix.vecMul_vecMul, hκ]
  have h21 : ∀ z, rowMul κ (rowMul κᴴ z) = z := fun z => by
    simp [rowMul_apply, Matrix.vecMul_vecMul, hκ']
  let e : (Fin 2 → ℂ) ≃L[ℝ] (Fin 2 → ℂ) :=
    ContinuousLinearEquiv.equivOfInverse (rowMul κ) (rowMul κᴴ) h12 h21
  let f' : SchwartzMap (Fin 2 → ℂ) ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ e f
  have hf' : ∀ v, f' v = f (rowMul κ v) := fun v => rfl
  refine ⟨f', fun v => hf' v, ?_⟩
  have hsem : ∀ i ∈ Finset.range (N + 1), ∀ j ∈ Finset.range (N + 1),
      SchwartzMap.seminorm ℝ i j f' ≤ 4 ^ N * SchwartzMap.seminorm ℝ i j f := by
    intro i hi j hj
    have hi' : i ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hj' : j ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    refine (seminorm_comp_le (rowMul κ) (rowMul κᴴ) h12 (norm_rowMul_le hb) (norm_rowMul_le hb')
      f f' hf' i j).trans ?_
    gcongr
    calc (2 : ℝ) ^ (i + j) ≤ 2 ^ (N + N) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 4 ^ N := by rw [pow_add, ← mul_pow]; norm_num
  unfold pS
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j hj => hsem i hi j hj

end GlobalTheory.CompanionTheory.UnitaryCompSchwartz
