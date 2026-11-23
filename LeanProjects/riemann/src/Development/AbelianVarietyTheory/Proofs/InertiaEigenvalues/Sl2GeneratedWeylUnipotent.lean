import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.SLGen

theorem exists_unif (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F] :
    ∃ ϖ : F, ϖ ≠ 0 ∧ ‖ϖ‖ < 1 ∧ ∀ y : F, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖ := by
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  have hK : IsCompact (Metric.ball (0 : F) 1) :=
    (isCompact_closedBall (0 : F) 1).of_isClosed_subset (IsUltrametricDist.isClosed_ball 0 1)
      Metric.ball_subset_closedBall
  obtain ⟨ϖ, hϖ, hmax⟩ := hK.exists_isMaxOn ⟨0, by simp⟩ continuous_norm.continuousOn
  have hϖ1 : ‖ϖ‖ < 1 := by simpa using hϖ
  have hle : ∀ y : F, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖ := fun y hy => hmax (by simpa using hy)
  obtain ⟨x, hx0, hx1⟩ := NormedField.exists_norm_lt_one F
  refine ⟨ϖ, ?_, hϖ1, hle⟩
  intro h
  have := hle x hx1
  rw [h, norm_zero] at this
  linarith

variable {F : Type} [Field F]

theorem nS_coe (z : F) : ((nS z : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, z; 0, 1] := rfl

theorem wS_coe : ((wS F : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl

theorem wS_inv_coe :
    (((wS F)⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, wS_coe, Matrix.adjugate_fin_two]; simp

theorem diag_coe {ϖ : F} (hϖ : ϖ ≠ 0) :
    ((nS ϖ * ((wS F)⁻¹ * nS ϖ⁻¹ * wS F) * nS ϖ * (wS F)⁻¹ : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = !![ϖ, 0; 0, ϖ⁻¹] := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, nS_coe, wS_coe, wS_inv_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hϖ] <;> field_simp <;> ring

theorem conj_step {ϖ : F} (hϖ : ϖ ≠ 0) (t : F) :
    (nS ϖ * ((wS F)⁻¹ * nS ϖ⁻¹ * wS F) * nS ϖ * (wS F)⁻¹)⁻¹ * nS t *
      (nS ϖ * ((wS F)⁻¹ * nS ϖ⁻¹ * wS F) * nS ϖ * (wS F)⁻¹) = nS (ϖ⁻¹ ^ 2 * t) := by
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, diag_coe hϖ, nS_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem decomp (g : SpecialLinearGroup (Fin 2) F) (hc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) :
    g = nS (((g : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) / (g : Matrix (Fin 2) (Fin 2) F) 1 0) *
      ((wS F)⁻¹ * nS (-(g : Matrix (Fin 2) (Fin 2) F) 1 0) * wS F) *
      nS (((g : Matrix (Fin 2) (Fin 2) F) 1 1 - 1) / (g : Matrix (Fin 2) (Fin 2) F) 1 0) := by
  have hdet := g.2
  rw [Matrix.det_fin_two] at hdet
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, nS_coe, wS_coe, wS_inv_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    first | ring1 | linear_combination -hdet | linear_combination -2 * hdet | linear_combination hdet |
      linear_combination 2 * hdet

theorem eq_top_of (H : Subgroup (SpecialLinearGroup (Fin 2) F)) (hw : wS F ∈ H) (hn : ∀ t, nS t ∈ H) :
    H = ⊤ := by
  have hl : ∀ c : F, (wS F)⁻¹ * nS (-c) * wS F ∈ H := fun c =>
    H.mul_mem (H.mul_mem (H.inv_mem hw) (hn _)) hw
  have key : ∀ g : SpecialLinearGroup (Fin 2) F, (g : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 → g ∈ H := by
    intro g hc
    rw [decomp g hc]
    exact H.mul_mem (H.mul_mem (hn _) (hl _)) (hn _)
  rw [eq_top_iff]
  intro g _
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · have hdet := g.2
    rw [Matrix.det_fin_two, hc] at hdet
    have ha : (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
      intro h; rw [h] at hdet; simp at hdet
    set L1 : SpecialLinearGroup (Fin 2) F := (wS F)⁻¹ * nS (-(1 : F)) * wS F
    have h1 : L1 * g ∈ H := by
      apply key
      simp only [L1, Matrix.SpecialLinearGroup.coe_mul, nS_coe, wS_coe, wS_inv_coe]
      simp [Matrix.mul_apply, Fin.sum_univ_two, hc, ha]
    have : g = L1⁻¹ * (L1 * g) := by group
    rw [this]
    exact H.mul_mem (H.inv_mem (hl 1)) h1
  · exact key g hc

end GlobalTheory.JR.SLGen

open GlobalTheory.JR.SLGen in

theorem GlobalTheory.JR.sl2_closure_weyl_unipotent_eq_top :
    ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
      [Unram F E], Subgroup.closure ({wS F} ∪ {g | ∃ t : F, (∀ y : F, ‖y‖ < 1 → ‖t * y‖ ≤ 1) ∧ g = nS t}) = ⊤ := by
  intro F E _ _ _ _ hU
  haveI : IsUltrametricDist F := hU.ultraF
  haveI : LocallyCompactSpace F := hU.lcF
  set H := Subgroup.closure ({wS F} ∪ {g | ∃ t : F, (∀ y : F, ‖y‖ < 1 → ‖t * y‖ ≤ 1) ∧ g = nS t})
  obtain ⟨ϖ, hϖ0, hϖ1, hmax⟩ := exists_unif F
  have hw : wS F ∈ H := Subgroup.subset_closure (Or.inl rfl)
  have hS : ∀ t : F, (∀ y : F, ‖y‖ < 1 → ‖t * y‖ ≤ 1) → nS t ∈ H := fun t ht =>
    Subgroup.subset_closure (Or.inr ⟨t, ht, rfl⟩)
  have hball : ∀ t : F, ‖t‖ ≤ 1 → nS t ∈ H := fun t ht => hS t fun y hy => by
    rw [norm_mul]; nlinarith [norm_nonneg t, norm_nonneg y]
  have hinv : nS ϖ⁻¹ ∈ H := hS _ fun y hy => by
    have hp : 0 < ‖ϖ‖ := norm_pos_iff.2 hϖ0
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ hp, mul_one]
    exact hmax y hy
  have hD : nS ϖ * ((wS F)⁻¹ * nS ϖ⁻¹ * wS F) * nS ϖ * (wS F)⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem (hball _ hϖ1.le)
      (H.mul_mem (H.mul_mem (H.inv_mem hw) hinv) hw)) (hball _ hϖ1.le)) (H.inv_mem hw)
  have hstep : ∀ t, nS t ∈ H → nS (ϖ⁻¹ ^ 2 * t) ∈ H := fun t ht => by
    rw [← conj_step hϖ0 t]
    exact H.mul_mem (H.mul_mem (H.inv_mem hD) ht) hD
  have hpow : ∀ k : ℕ, ∀ t, nS t ∈ H → nS ((ϖ⁻¹ ^ 2) ^ k * t) ∈ H := by
    intro k
    induction k with
    | zero => intro t ht; simpa using ht
    | succ k ih => intro t ht; rw [pow_succ', mul_assoc]; exact hstep _ (ih t ht)
  have hall : ∀ x : F, nS x ∈ H := by
    intro x
    have hq : ‖ϖ ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg ϖ]
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (‖x‖ + 1) by positivity) hq
    have h1 : ‖(ϖ ^ 2) ^ k * x‖ ≤ 1 := by
      rw [norm_mul, norm_pow]
      rw [lt_div_iff₀ (by positivity)] at hk
      nlinarith [norm_nonneg x, pow_nonneg (norm_nonneg (ϖ ^ 2)) k]
    have e : x = (ϖ⁻¹ ^ 2) ^ k * ((ϖ ^ 2) ^ k * x) := by
      rw [← mul_assoc, ← mul_pow, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hϖ0), one_pow, one_mul]
    rw [e]
    exact hpow k _ (hball _ h1)
  exact eq_top_of H hw hall
