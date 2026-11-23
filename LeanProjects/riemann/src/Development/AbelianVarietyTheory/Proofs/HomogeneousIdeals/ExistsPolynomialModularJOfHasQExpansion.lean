import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HasQExpansionModularForm

open UpperHalfPlane ModularForm Complex Function Filter PowerSeries
open scoped Topology MatrixGroups Manifold Real ArithmeticFunction.sigma

noncomputable section

namespace GlobalTheory

local notation "𝕢" => Function.Periodic.qParam

def modularJ (τ : ℍ) : ℂ := E₄ τ ^ 3 / discriminant τ

lemma modularJ_def (τ : ℍ) : modularJ τ = E₄ τ ^ 3 / discriminant τ := rfl

lemma modularJ_smul (γ : SL(2, ℤ)) (τ : ℍ) : modularJ (γ • τ) = modularJ τ := by
  have hγ : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have h1 := SlashInvariantForm.slash_action_eqn'' E₄ hγ τ
  have h2 := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγ τ
  have h3 := denom_ne_zero (γ : GL (Fin 2) ℝ) τ
  have h4 := discriminant_ne_zero τ
  change E₄ ((γ : GL (Fin 2) ℝ) • τ) ^ 3 / CuspForm.discriminant ((γ : GL (Fin 2) ℝ) • τ) =
    E₄ τ ^ 3 / CuspForm.discriminant τ
  rw [h1, h2]
  change _ / (_ * discriminant τ) = _ / discriminant τ
  field_simp

lemma mdifferentiable_modularJ : MDiff modularJ :=
  (E₄.holo'.pow 3).div CuspForm.discriminant.holo' discriminant_ne_zero

lemma periodic_comp_ofComplex_of_vadd {f : ℍ → ℂ} {h : ℝ} (hf : ∀ τ : ℍ, f (h +ᵥ τ) = f τ) :
    Periodic (f ∘ ofComplex) (h : ℂ) := by
  intro w
  by_cases! hw : 0 < im w
  · have : 0 < im (w + h) := by simp [hw]
    simp only [comp_apply, ofComplex_apply_of_im_pos this, ofComplex_apply_of_im_pos hw]
    convert! hf ⟨w, hw⟩ using 2
    ext
    simp [add_comm]
  · have : im (w + h) ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos this, ofComplex_apply_of_im_nonpos hw]

lemma qParam_one_vadd (τ : ℍ) : 𝕢 1 ((1 : ℝ) +ᵥ τ : ℍ) = 𝕢 1 τ := by
  simp [Periodic.qParam, mul_add, Complex.exp_add]

lemma hasQExpansion_qParam_pow_mul {f : ℍ → ℂ} (hinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ)
    (hhol : MDiff f) {m : ℕ} (hbdd : IsBoundedAtImInfty fun τ : ℍ ↦ 𝕢 1 τ ^ m * f τ) :
    HasQExpansion 1 (fun τ ↦ 𝕢 1 τ ^ m * f τ) (qExpansion 1 fun τ ↦ 𝕢 1 τ ^ m * f τ) := by
  refine .of_periodic one_pos (periodic_comp_ofComplex_of_vadd fun τ ↦ ?_) ?_ hbdd
  · rw [qParam_one_vadd, ← modular_T_smul, hinv]
  · exact (((HasQExpansion.qParam 1).mdifferentiable one_pos).pow m).mul hhol

lemma twelve_dvd_sigma (n : ℕ) : (12 : ℤ) ∣ 5 * (σ 3 n : ℤ) + 7 * (σ 5 n : ℤ) := by
  simp only [ArithmeticFunction.sigma_apply, Nat.cast_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.dvd_sum fun d _ ↦ ?_
  have : ∀ x : ZMod 12, 5 * x ^ 3 + 7 * x ^ 5 = 0 := by decide
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 12).mp
  push_cast
  exact this d

lemma qExpansion_E₄ : qExpansion 1 E₄ =
    PowerSeries.map (Int.castRingHom ℂ) (1 + 240 * PowerSeries.mk fun n ↦ (σ 3 n : ℤ)) := by
  ext m
  rw [EisensteinSeries.E_qExpansion_coeff _ ⟨2, rfl⟩, show bernoulli 4 = -1 / 30 by decide +kernel]
  rw [coeff_map, show (240 : ℤ⟦X⟧) = C 240 from rfl, map_add, coeff_C_mul, coeff_one]
  split_ifs with hm
  · simp [hm]
  · simp; norm_num

lemma qExpansion_E₆ : qExpansion 1 E₆ =
    PowerSeries.map (Int.castRingHom ℂ) (1 - 504 * PowerSeries.mk fun n ↦ (σ 5 n : ℤ)) := by
  ext m
  rw [EisensteinSeries.E_qExpansion_coeff _ ⟨3, rfl⟩, show bernoulli 6 = 1 / 42 by decide +kernel]
  rw [coeff_map, show (504 : ℤ⟦X⟧) = C 504 from rfl, map_sub, coeff_C_mul, coeff_one]
  split_ifs with hm
  · simp [hm]
  · simp; norm_num

lemma exists_hasQExpansion_discriminant : ∃ U : ℤ⟦X⟧, coeff 0 U = 1 ∧
    HasQExpansion 1 discriminant (X * PowerSeries.map (Int.castRingHom ℂ) U) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk fun n ↦ (σ 3 n : ℤ) with hA
  set B : ℤ⟦X⟧ := PowerSeries.mk fun n ↦ (σ 5 n : ℤ) with hB
  obtain ⟨S, hS⟩ : ∃ S : ℤ⟦X⟧, 5 * A + 7 * B = 12 * S := by
    choose c hc using twelve_dvd_sigma
    refine ⟨PowerSeries.mk c, ?_⟩
    ext n
    rw [show (5 : ℤ⟦X⟧) = C 5 from rfl, show (7 : ℤ⟦X⟧) = C 7 from rfl,
      show (12 : ℤ⟦X⟧) = C 12 from rfl, map_add, coeff_C_mul, coeff_C_mul, coeff_C_mul]
    simpa [hA, hB] using hc n
  set D : ℤ⟦X⟧ := S + 100 * A ^ 2 + 8000 * A ^ 3 - 147 * B ^ 2 with hD
  have hD' : (1 + 240 * A) ^ 3 - (1 - 504 * B) ^ 2 = 1728 * D := by
    rw [hD]; linear_combination 144 * hS
  have h1 := (HasQExpansion.const 1 (1728⁻¹ : ℂ)).mul
    (((hasQExpansion_modularForm E₄).pow 3).sub ((hasQExpansion_modularForm E₆).pow 2))
  rw [qExpansion_E₄, qExpansion_E₆, ← map_pow, ← map_pow, ← map_sub, hD', map_mul, ← mul_assoc,
    show (C (1728⁻¹ : ℂ) * PowerSeries.map (Int.castRingHom ℂ) 1728 : ℂ⟦X⟧) = 1 by
      rw [show (1728 : ℤ⟦X⟧) = C 1728 from rfl, map_C, ← map_mul]; simp, one_mul] at h1
  have h2 : HasQExpansion 1 discriminant (PowerSeries.map (Int.castRingHom ℂ) D) :=
    h1.congr fun τ ↦ by rw [discriminant_eq_E₄_cube_sub_E₆_sq]; ring
  have h3 : HasQExpansion 1 discriminant (qExpansion 1 discriminant) := fun τ ↦
    ModularForm.hasSum_qExpansion CuspForm.discriminant one_pos one_mem_strictPeriods_SL τ
  have h4 := h2.unique one_pos h3
  have h5 : coeff 0 D = 0 := by
    have := CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos
      one_mem_strictPeriods_SL
    rw [CuspForm.coe_discriminant, ← h4, coeff_map] at this
    simpa using this
  have h6 : coeff 1 D = 1 := by
    have := discriminant_qExpansion_coeff_one
    rw [← h4, coeff_map] at this
    simpa using this
  obtain ⟨U, hU⟩ : X ∣ D := X_dvd_iff.mpr (by simpa using h5)
  refine ⟨U, by rw [← h6, hU, coeff_succ_X_mul], ?_⟩
  rwa [hU, map_mul, map_X] at h2

theorem exists_hasQExpansion_modularJ : ∃ J : ℤ⟦X⟧, coeff 0 J = 1 ∧
    HasQExpansion 1 (fun τ ↦ 𝕢 1 τ * modularJ τ) (PowerSeries.map (Int.castRingHom ℂ) J) := by
  obtain ⟨U, hU0, hU⟩ := exists_hasQExpansion_discriminant
  have hq (τ : ℍ) : 𝕢 1 τ ≠ 0 := Periodic.qParam_ne_zero _
  have hu : HasQExpansion 1 (fun τ ↦ discriminant τ / 𝕢 1 τ)
      (PowerSeries.map (Int.castRingHom ℂ) U) :=
    .of_qParam_mul (hU.congr fun τ ↦ by field_simp [hq τ])
  have hE := (hasQExpansion_modularForm E₄).pow 3
  have heq (τ : ℍ) : 𝕢 1 τ ^ 1 * modularJ τ = E₄ τ ^ 3 / (discriminant τ / 𝕢 1 τ) := by
    rw [modularJ_def]; field_simp
  have hbdd : IsBoundedAtImInfty fun τ : ℍ ↦ 𝕢 1 τ ^ 1 * modularJ τ := by
    simp_rw [heq]
    exact ((hE.tendsto one_pos).div (hu.tendsto one_pos) (by simp [hU0])).isBigO_one ℝ
  have h1 := hasQExpansion_qParam_pow_mul modularJ_smul mdifferentiable_modularJ hbdd
  set φ := qExpansion 1 fun τ : ℍ ↦ 𝕢 1 τ ^ 1 * modularJ τ
  have h2 := (h1.mul hu).unique one_pos (hE.congr fun τ ↦ by
    rw [modularJ_def]; field_simp [hq τ, discriminant_ne_zero τ])
  rw [qExpansion_E₄, ← map_pow] at h2
  set E : ℤ⟦X⟧ := (1 + 240 * PowerSeries.mk fun n ↦ (σ 3 n : ℤ)) ^ 3 with hE'
  have hUV : U * U.invOfUnit 1 = 1 := mul_invOfUnit U 1 (by simpa using hU0)
  refine ⟨E * U.invOfUnit 1, by simp [hE'], ?_⟩
  rw [map_mul, ← h2, mul_assoc, ← map_mul, hUV, map_one, mul_one]
  simpa using h1

theorem exists_polynomial_modularJ_of_hasQExpansion (A : AddSubgroup ℂ) {m : ℕ} {f : ℍ → ℂ}
    {φ : ℂ⟦X⟧} (hinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ)
    (hf : HasQExpansion 1 (fun τ ↦ 𝕢 1 τ ^ m * f τ) φ) (hA : ∀ k, coeff k φ ∈ A) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ m ∧ P.coeff m = coeff 0 φ ∧ (∀ i, P.coeff i ∈ A) ∧
      ∀ τ, f τ = P.eval (modularJ τ) := by
  induction m generalizing f φ with
  | zero =>
    simp only [pow_zero, one_mul] at hf
    have hs (γ : SL(2, ℤ)) : f ∣[(0 : ℤ)] γ = f := by
      ext τ; simpa [SL_slash_apply] using hinv γ τ
    let F : ModularForm 𝒮ℒ 0 :=
      { toFun := f
        slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ hs γ
        holo' := hf.mdifferentiable one_pos
        bdd_at_cusps' := fun {c} hc ↦ by
          rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
          rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
          intro γ _
          rw [hs γ]
          exact hf.isBoundedAtImInfty one_pos }
    obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const F
    have hc' : f = fun _ ↦ c := hc
    have h0 : φ = C c := hf.unique one_pos (hc' ▸ HasQExpansion.const 1 c)
    have h1 : c ∈ A := by simpa [h0] using hA 0
    refine ⟨Polynomial.C c, by simp, by simp [h0], fun i ↦ ?_, fun τ ↦ by simp [hc']⟩
    rw [Polynomial.coeff_C]
    split_ifs
    exacts [h1, A.zero_mem]
  | succ m ih =>
    obtain ⟨J, hJ0, hJ⟩ := exists_hasQExpansion_modularJ
    set c := coeff 0 φ with hc
    have h1 := hf.sub ((HasQExpansion.const 1 c).mul (hJ.pow (m + 1)))
    set ψ := φ - C c * PowerSeries.map (Int.castRingHom ℂ) J ^ (m + 1) with hψ
    have hψA (k : ℕ) : coeff k ψ ∈ A := by
      rw [hψ, map_sub, coeff_C_mul, ← map_pow, coeff_map]
      refine A.sub_mem (hA k) ?_
      simpa [mul_comm, hc] using A.zsmul_mem (hA 0) (coeff k (J ^ (m + 1)))
    obtain ⟨χ, hχ⟩ : X ∣ ψ := X_dvd_iff.mpr (by
      have : constantCoeff (PowerSeries.map (Int.castRingHom ℂ) J) = 1 := by
        rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, hJ0, map_one]
      simp [hψ, hc, this])
    have h2 : HasQExpansion 1 (fun τ ↦ 𝕢 1 τ ^ m * (f τ - c * modularJ τ ^ (m + 1))) χ :=
      .of_qParam_mul (hχ ▸ h1.congr fun τ ↦ by ring)
    obtain ⟨P, hP1, -, hP3, hP4⟩ := ih (fun γ τ ↦ by rw [hinv, modularJ_smul]) h2
      (fun k ↦ by simpa [hχ, coeff_succ_X_mul] using hψA (k + 1))
    refine ⟨P + Polynomial.monomial (m + 1) c, ?_, ?_, fun i ↦ ?_, fun τ ↦ ?_⟩
    · exact Polynomial.natDegree_add_le_of_degree_le (by omega)
        (Polynomial.natDegree_monomial_le _)
    · simp [Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_le hP1)]
    · rw [Polynomial.coeff_add, Polynomial.coeff_monomial]
      refine A.add_mem (hP3 i) ?_
      split_ifs
      exacts [hA 0, A.zero_mem]
    · simp [← hP4]

theorem exists_polynomial_modularJ {m : ℕ} {f : ℍ → ℂ}
    (hinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ) (hhol : MDiff f)
    (hbdd : IsBoundedAtImInfty fun τ : ℍ ↦ 𝕢 1 τ ^ m * f τ) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ m ∧
      P.coeff m = coeff 0 (qExpansion 1 fun τ ↦ 𝕢 1 τ ^ m * f τ) ∧
      (∀ i, P.coeff i ∈ AddSubgroup.closure
        (Set.range fun k ↦ coeff k (qExpansion 1 fun τ ↦ 𝕢 1 τ ^ m * f τ))) ∧
      ∀ τ, f τ = P.eval (modularJ τ) :=
  exists_polynomial_modularJ_of_hasQExpansion _ hinv (hasQExpansion_qParam_pow_mul hinv hhol hbdd)
    fun k ↦ AddSubgroup.subset_closure ⟨k, rfl⟩

end GlobalTheory
