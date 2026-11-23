import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.RightKTypes.KlfStepCoefApply
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.RightKTypes.BaseAct
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.RightKTypes.StepCoefApply
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.RightKTypes.RightExp

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace CompanionTheory.RgExh.Dec.L.WyKR

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem kr_dom {ι : Type} [Fintype ι] (γ h : ι → ℂ) (B : ℝ) (hγ : ∀ a, ‖γ a‖ ≤ B) :
    ‖∑ a, γ a * h a‖ ^ 2 ≤ (Fintype.card ι * B ^ 2) * ∑ a, ‖h a‖ ^ 2 := by
  have h1 : ‖∑ a, γ a * h a‖ ≤ |B| * ∑ a, ‖h a‖ := by
    calc _ ≤ ∑ a, ‖γ a * h a‖ := norm_sum_le _ _
      _ ≤ ∑ a, |B| * ‖h a‖ := sum_le_sum fun a _ => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right ((hγ a).trans (le_abs_self B)) (norm_nonneg _)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun a => ‖h a‖)
  calc ‖∑ a, γ a * h a‖ ^ 2 ≤ (|B| * ∑ a, ‖h a‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = B ^ 2 * (∑ a, ‖h a‖) ^ 2 := by rw [mul_pow, sq_abs]
    _ ≤ B ^ 2 * (Fintype.card ι * ∑ a, ‖h a‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg B)
        simpa using h2
    _ = _ := by ring

theorem kr_img {ι κ : Type} [Fintype ι] [DecidableEq κ] (p : ι → κ) (f : κ → ℝ) (hf : ∀ q, 0 ≤ f q) :
    ∑ a, f (p a) ≤ Fintype.card ι * ∑ q ∈ Finset.univ.image p, f q := by
  calc ∑ a, f (p a) ≤ ∑ _a : ι, ∑ q ∈ Finset.univ.image p, f q :=
        sum_le_sum fun a _ => Finset.single_le_sum (fun q _ => hf q) (Finset.mem_image_of_mem p (Finset.mem_univ a))
    _ = _ := by simp

theorem kRight : KRight := by
  intro n ε H _ _ _ σ D E hK χ ss hU i u
  classical
  have hL := leftExp_path (leftExp_base hK hU) χ ss
  have hC := contFam_path (contFam_base hK hU) χ ss
  have hR := rightEq_path (baseAct hK hU) (rightEq_base hK hU) χ ss
  refine ⟨hC i u, ?_⟩
  obtain ⟨r, is, β, B, hβ, hLi⟩ := hL i
  obtain ⟨r', w, a, B', ha, hw⟩ := rightExp (pathAct (baseAct hK hU) χ ss) u
  let p : Fin r × Fin r' → (D × List (Fin n)) × (path ⟨D, E, hK.gl⟩ χ ss).V := fun q => (is q.1, w q.2)
  refine ⟨Finset.univ.image p, Fintype.card (Fin r × Fin r') * (|B| * |B'|) ^ 2 * Fintype.card (Fin r × Fin r'),
    fun g k k' => ?_⟩
  have e1 : famP σ D E hK.gl χ ss i u (S7.toMK k * S7.toM g * S7.toMK k') =
      ∑ q : Fin r × Fin r', (β q.1 k * a q.2 k') * famP σ D E hK.gl χ ss (p q).1 (p q).2 (S7.toM g) := by
    have h1 := hR i u ((k : S7.UJ ε) * g) k'
    have h2 := hLi ((pathAct (baseAct hK hU) χ ss).ρ k' u) g k
    have e0 : S7.toM ((k : S7.UJ ε) * g) = S7.toMK k * S7.toM g := rfl
    rw [e0] at h1
    simp only [famP]
    rw [h1, h2, hw k', Fintype.sum_prod_type]
    refine sum_congr rfl fun l _ => ?_
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, p]
    exact sum_congr rfl fun m _ => by ring
  rw [e1]
  refine (kr_dom _ _ (|B| * |B'|) fun q => ?_).trans ?_
  · rw [norm_mul]
    exact mul_le_mul ((hβ _ _).trans (le_abs_self B)) ((ha _ _).trans (le_abs_self B')) (norm_nonneg _)
      (abs_nonneg B)
  · have h3 := kr_img p (fun q => ‖famP σ D E hK.gl χ ss q.1 q.2 (S7.toM g)‖ ^ 2) (fun q => sq_nonneg _)
    calc (Fintype.card (Fin r × Fin r') * (|B| * |B'|) ^ 2) *
          ∑ q, ‖famP σ D E hK.gl χ ss (p q).1 (p q).2 (S7.toM g)‖ ^ 2
        ≤ (Fintype.card (Fin r × Fin r') * (|B| * |B'|) ^ 2) *
          (Fintype.card (Fin r × Fin r') * ∑ q ∈ Finset.univ.image p, ‖famP σ D E hK.gl χ ss q.1 q.2 (S7.toM g)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by ring

end CompanionTheory.RgExh.Dec.L.WyKR
