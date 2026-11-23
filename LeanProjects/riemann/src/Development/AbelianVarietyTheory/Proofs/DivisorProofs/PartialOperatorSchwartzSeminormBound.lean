import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTemperateGrowthElim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClmSupBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowNormMulSeminormSliceRLe

open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff

noncomputable section
namespace GlobalTheory.SliceOpDecay

theorem norm_le_max_comp {V : Type} [NormedAddCommGroup V] {κ κ₁' : Type} [Fintype κ] [Fintype κ₁']
    (z : κ ⊕ κ₁' → V) : ‖z‖ ≤ max ‖z ∘ Sum.inl‖ ‖z ∘ Sum.inr‖ := by
  refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).2 fun i => ?_
  cases i with
  | inl i => exact (norm_le_pi_norm (z ∘ Sum.inl) i).trans (le_max_left _ _)
  | inr j => exact (norm_le_pi_norm (z ∘ Sum.inr) j).trans (le_max_right _ _)

theorem pow_norm_le_add {V : Type} [NormedAddCommGroup V] {κ κ₁' : Type} [Fintype κ] [Fintype κ₁']
    (z : κ ⊕ κ₁' → V) (k : ℕ) : ‖z‖ ^ k ≤ ‖z ∘ Sum.inl‖ ^ k + ‖z ∘ Sum.inr‖ ^ k := by
  have h := pow_le_pow_left₀ (norm_nonneg z) (norm_le_max_comp z) k
  rcases le_total ‖z ∘ Sum.inl‖ ‖z ∘ Sum.inr‖ with hle | hle
  · rw [max_eq_right hle] at h; linarith [pow_nonneg (norm_nonneg (z ∘ Sum.inl)) k]
  · rw [max_eq_left hle] at h; linarith [pow_nonneg (norm_nonneg (z ∘ Sum.inr)) k]

theorem decay (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (κ κ' κ₁' : Type) [Fintype κ] [Fintype κ'] [Fintype κ₁']
    (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (k : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (z : κ ⊕ κ₁' → V),
      ‖z‖ ^ k * ‖qOp P f z‖ ≤ C * s.sup (schwartzSeminormFamily ℂ (κ ⊕ κ' → V) ℂ) f := by
  obtain ⟨s1, C1, hC1, h1⟩ := clm_sup_bound P {(k, 0)}
  obtain ⟨s2, C2, hC2, h2⟩ := clm_sup_bound P {(0, 0)}
  let sh : ℕ × ℕ → ℕ × ℕ := fun i => (k + i.1, i.2)
  refine ⟨s1 ∪ s2.image sh, C1 + C2, add_nonneg hC1 hC2, fun f z => ?_⟩
  set F := schwartzSeminormFamily ℂ (κ ⊕ κ' → V) ℂ
  set x := z ∘ Sum.inl
  set y := z ∘ Sum.inr
  set g := sliceR f x
  have hq : qOp P f z = P g y := rfl
  set S := (s1 ∪ s2.image sh).sup F f
  have hS0 : 0 ≤ S := apply_nonneg _ _

  have hy : ‖y‖ ^ k * ‖P g y‖ ≤ C1 * S := by
    have a1 : ‖y‖ ^ k * ‖P g y‖ ≤ SchwartzMap.seminorm ℂ k 0 (P g) := by
      have := SchwartzMap.le_seminorm ℂ k 0 (P g) y
      simpa [norm_iteratedFDeriv_zero] using this
    have a2 := h1 g
    simp only [Finset.sup_singleton, SchwartzMap.schwartzSeminormFamily_apply] at a2
    have a3 : s1.sup (schwartzSeminormFamily ℂ (κ' → V) ℂ) g ≤ S := by
      refine Seminorm.finset_sup_apply_le hS0 fun i hi => ?_
      have w := GlobalTheory.SliceWeight.pow_norm_mul_seminorm_sliceR_le V κ κ' f 0 i.1 i.2 x
      simp only [pow_zero, one_mul, zero_add] at w
      refine le_trans (b := SchwartzMap.seminorm ℂ _ _ f) w ?_
      have : F i f ≤ S := Seminorm.le_finset_sup_apply (Finset.mem_union_left _ hi)
      exact this
    calc _ ≤ _ := a1
      _ ≤ _ := a2
      _ ≤ C1 * S := by gcongr

  have hx : ‖x‖ ^ k * ‖P g y‖ ≤ C2 * S := by
    have a1 : ‖P g y‖ ≤ SchwartzMap.seminorm ℂ 0 0 (P g) := SchwartzMap.norm_le_seminorm ℂ (P g) y
    have a2 := h2 g
    simp only [Finset.sup_singleton, SchwartzMap.schwartzSeminormFamily_apply] at a2
    have a3 : ‖x‖ ^ k * s2.sup (schwartzSeminormFamily ℂ (κ' → V) ℂ) g ≤ S := by
      have e : ‖x‖ ^ k * s2.sup (schwartzSeminormFamily ℂ (κ' → V) ℂ) g
          = s2.sup (schwartzSeminormFamily ℂ (κ' → V) ℂ) (((‖x‖ ^ k : ℝ) : ℂ) • g) := by
        rw [map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
      rw [e]
      refine Seminorm.finset_sup_apply_le hS0 fun i hi => ?_
      rw [map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
      have w := GlobalTheory.SliceWeight.pow_norm_mul_seminorm_sliceR_le V κ κ' f k i.1 i.2 x
      refine le_trans (b := SchwartzMap.seminorm ℂ _ _ f) w ?_
      have : F (sh i) f ≤ S :=
        Seminorm.le_finset_sup_apply (Finset.mem_union_right _ (Finset.mem_image_of_mem sh hi))
      simpa [F, sh, SchwartzMap.schwartzSeminormFamily_apply] using this
    calc ‖x‖ ^ k * ‖P g y‖ ≤ ‖x‖ ^ k * (C2 * s2.sup (schwartzSeminormFamily ℂ (κ' → V) ℂ) g) := by
          gcongr; exact a1.trans a2
      _ = C2 * (‖x‖ ^ k * s2.sup (schwartzSeminormFamily ℂ (κ' → V) ℂ) g) := by ring
      _ ≤ C2 * S := by gcongr
  rw [hq]
  calc ‖z‖ ^ k * ‖P g y‖ ≤ (‖x‖ ^ k + ‖y‖ ^ k) * ‖P g y‖ := by
        gcongr; exact pow_norm_le_add z k
    _ = ‖x‖ ^ k * ‖P g y‖ + ‖y‖ ^ k * ‖P g y‖ := by ring
    _ ≤ C2 * S + C1 * S := add_le_add hx hy
    _ = (C1 + C2) * S := by ring

end GlobalTheory.SliceOpDecay
