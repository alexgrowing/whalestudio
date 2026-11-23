import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivSchwartzCompClmLe

open scoped SchwartzMap ContDiff

noncomputable section
namespace GlobalTheory.SchwartzExtend

theorem norm_iteratedFDeriv_comp_clm_le {Y F : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : Y →L[ℝ] F) (f : 𝓢(F, ℂ)) (i : ℕ) (y : Y) :
    ‖iteratedFDeriv ℝ i (fun z => f (L z)) y‖ ≤ ‖iteratedFDeriv ℝ i f (L y)‖ * ‖L‖ ^ i := by
  first
  | exact @_root_.GlobalTheory.SchwartzDerivativeCompositionBound.norm_iteratedFDeriv_schwartz_comp_clm_le
  | exact _root_.GlobalTheory.SchwartzDerivativeCompositionBound.norm_iteratedFDeriv_schwartz_comp_clm_le
  | (apply _root_.GlobalTheory.SchwartzDerivativeCompositionBound.norm_iteratedFDeriv_schwartz_comp_clm_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.SchwartzDerivativeCompositionBound.norm_iteratedFDeriv_schwartz_comp_clm_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SchwartzDerivativeCompositionBound.norm_iteratedFDeriv_schwartz_comp_clm_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SchwartzDerivativeCompositionBound.norm_iteratedFDeriv_schwartz_comp_clm_le ..)

theorem pow_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) :
    (a + b) ^ k ≤ 2 ^ k * (a ^ k + b ^ k) := by
  have hm : a + b ≤ 2 * max a b := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have h1 : (a + b) ^ k ≤ (2 * max a b) ^ k := pow_le_pow_left₀ (by positivity) hm k
  rw [mul_pow] at h1
  refine h1.trans ?_
  gcongr
  have p1 := pow_nonneg ha k
  have p2 := pow_nonneg hb k
  rcases le_total a b with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

theorem exists_schwartz_eq_one_zero (C : Type) [NormedAddCommGroup C] [NormedSpace ℝ C]
    [FiniteDimensional ℝ C] : ∃ χ : 𝓢(C, ℂ), χ 0 = 1 := by
  let b : ContDiffBump (0 : C) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  have h2 : ContDiff ℝ ∞ (fun x => ((b x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  refine ⟨h1.toSchwartzMap h2, ?_⟩
  show ((b 0 : ℝ) : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
  simp

def extCLM {Y F₁ F₂ : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    (L₁ : Y →L[ℝ] F₁) (L₂ : Y →L[ℝ] F₂) (hL : ∀ y, ‖y‖ ≤ ‖L₁ y‖ + ‖L₂ y‖) (χ : 𝓢(F₂, ℂ)) :
    𝓢(F₁, ℂ) →L[ℂ] 𝓢(Y, ℂ) :=
  SchwartzMap.mkCLM (σ := RingHom.id ℂ) (fun φ y => φ (L₁ y) * χ (L₂ y))
    (fun φ ψ y => by simp [add_mul])
    (fun a φ y => by simp [smul_eq_mul, mul_assoc])
    (fun φ => ((φ.smooth ⊤).comp L₁.contDiff).mul ((χ.smooth ⊤).comp L₂.contDiff))
    (by
      rintro ⟨k, m⟩
      refine ⟨Finset.range (k + 1) ×ˢ Finset.range (m + 1),
        2 ^ k * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ‖L₁‖ ^ i * ‖L₂‖ ^ (m - i) *
          (SchwartzMap.seminorm ℂ 0 (m - i) χ + SchwartzMap.seminorm ℂ k (m - i) χ), by positivity,
        fun φ y => ?_⟩
      set S := (Finset.range (k + 1) ×ˢ Finset.range (m + 1)).sup (schwartzSeminormFamily ℂ F₁ ℂ) φ
      have hS : ∀ j ≤ k, ∀ i ≤ m, SchwartzMap.seminorm ℂ j i φ ≤ S := fun j hj i hi => by
        have := Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ F₁ ℂ) (x := φ)
          (s := Finset.range (k + 1) ×ˢ Finset.range (m + 1)) (i := (j, i))
          (Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega), Finset.mem_range.2 (by omega)⟩)
        simpa [SchwartzMap.schwartzSeminormFamily_apply] using this
      have hs₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Y => φ (L₁ z)) := (φ.smooth ⊤).comp L₁.contDiff
      have hs₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Y => χ (L₂ z)) := (χ.smooth ⊤).comp L₂.contDiff
      have hLe := norm_iteratedFDeriv_mul_le hs₁ hs₂ y (n := m) (by exact_mod_cast le_top)
      have hy : ‖y‖ ^ k ≤ 2 ^ k * (‖L₁ y‖ ^ k + ‖L₂ y‖ ^ k) :=
        (pow_le_pow_left₀ (norm_nonneg _) (hL y) k).trans (pow_add_le _ _ (norm_nonneg _) (norm_nonneg _) k)
      show ‖y‖ ^ k * ‖iteratedFDeriv ℝ m (fun z => φ (L₁ z) * χ (L₂ z)) y‖ ≤ _
      calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ m (fun z => φ (L₁ z) * χ (L₂ z)) y‖
          ≤ (2 ^ k * (‖L₁ y‖ ^ k + ‖L₂ y‖ ^ k)) * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
              (‖iteratedFDeriv ℝ i φ (L₁ y)‖ * ‖L₁‖ ^ i) *
              (‖iteratedFDeriv ℝ (m - i) χ (L₂ y)‖ * ‖L₂‖ ^ (m - i)) := by
            refine mul_le_mul hy (hLe.trans ?_) (norm_nonneg _) (by positivity)
            refine Finset.sum_le_sum fun i _ => ?_
            gcongr
            · exact norm_iteratedFDeriv_comp_clm_le L₁ φ i y
            · exact norm_iteratedFDeriv_comp_clm_le L₂ χ (m - i) y
        _ = 2 ^ k * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ‖L₁‖ ^ i * ‖L₂‖ ^ (m - i) *
              ((‖L₁ y‖ ^ k * ‖iteratedFDeriv ℝ i φ (L₁ y)‖) * ‖iteratedFDeriv ℝ (m - i) χ (L₂ y)‖ +
               ‖iteratedFDeriv ℝ i φ (L₁ y)‖ * (‖L₂ y‖ ^ k * ‖iteratedFDeriv ℝ (m - i) χ (L₂ y)‖)) := by
            rw [mul_assoc, Finset.mul_sum]
            congr 1
            exact Finset.sum_congr rfl fun i _ => by ring
        _ ≤ 2 ^ k * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ‖L₁‖ ^ i * ‖L₂‖ ^ (m - i) *
              (S * SchwartzMap.seminorm ℂ 0 (m - i) χ + S * SchwartzMap.seminorm ℂ k (m - i) χ) := by
            gcongr with i hi
            · exact (SchwartzMap.le_seminorm ℂ k i φ _).trans (hS k le_rfl i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))
            · exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ χ _ _
            · exact (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ φ _ _).trans (hS 0 (Nat.zero_le _) i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))
            · exact SchwartzMap.le_seminorm ℂ k (m - i) χ _
        _ = _ := by
            rw [mul_assoc, Finset.sum_mul]
            congr 1
            exact Finset.sum_congr rfl fun i _ => by ring)

theorem extCLM_apply {Y F₁ F₂ : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    (L₁ : Y →L[ℝ] F₁) (L₂ : Y →L[ℝ] F₂) (hL : ∀ y, ‖y‖ ≤ ‖L₁ y‖ + ‖L₂ y‖) (χ : 𝓢(F₂, ℂ))
    (φ : 𝓢(F₁, ℂ)) (y : Y) : extCLM L₁ L₂ hL χ φ y = φ (L₁ y) * χ (L₂ y) := rfl

theorem exists_extend_clm {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (P : Submodule ℝ Y) :
    ∃ E : SchwartzMap P ℂ →L[ℂ] SchwartzMap Y ℂ, ∀ (φ : SchwartzMap P ℂ) (p : P), E φ (p : Y) = φ p := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl P
  let π₁ : Y →L[ℝ] P := LinearMap.toContinuousLinearMap (Submodule.linearProjOfIsCompl P C hC)
  let π₂ : Y →L[ℝ] C := LinearMap.toContinuousLinearMap (Submodule.linearProjOfIsCompl C P hC.symm)
  have hL : ∀ y, ‖y‖ ≤ ‖π₁ y‖ + ‖π₂ y‖ := fun y => by
    have e : ((Submodule.linearProjOfIsCompl P C hC y : P) : Y) +
        ((Submodule.linearProjOfIsCompl C P hC.symm y : C) : Y) = y :=
      Submodule.projection_add_projection_eq_self hC y
    calc ‖y‖ = ‖((Submodule.linearProjOfIsCompl P C hC y : P) : Y) +
          ((Submodule.linearProjOfIsCompl C P hC.symm y : C) : Y)‖ := by rw [e]
      _ ≤ _ := norm_add_le _ _
  obtain ⟨χ, hχ⟩ := exists_schwartz_eq_one_zero C
  refine ⟨extCLM π₁ π₂ hL χ, fun φ p => ?_⟩
  rw [extCLM_apply]
  have h1 : π₁ (p : Y) = p := Submodule.linearProjOfIsCompl_apply_left hC p
  have h2 : π₂ (p : Y) = 0 := Submodule.linearProjOfIsCompl_apply_right hC.symm p
  rw [h1, h2, hχ, mul_one]

theorem extend_clm_of_submodule : ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] (P : Submodule ℝ Y),
    ∃ E : SchwartzMap P ℂ →L[ℂ] SchwartzMap Y ℂ, ∀ (φ : SchwartzMap P ℂ) (p : P), E φ (p : Y) = φ p :=
  fun P => exists_extend_clm P

end GlobalTheory.SchwartzExtend
