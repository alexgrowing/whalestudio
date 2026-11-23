import Formalism.HermitianCurvature.StatementE

namespace Formalism.FourierDecayAlt.P.E2

open Formalism.FourierDecayAlt.E Real Polynomial MeasureTheory

theorem middleThird_ok : MiddleThird := by
  intro n lam α β Y hI hroot hY1 hY2
  have hL : 0 < β - α := by linarith
  have key : ∀ s, (β-α)/3 ≤ |Y + lam s| := by
    intro s
    have h := hroot s
    simp only [Set.mem_Ioo, not_and_or, not_lt] at h
    rcases h with h | h
    · rw [le_abs]; left; linarith
    · rw [le_abs]; right; linarith
  have key2 : ∀ s, (β-α)/4 ≤ |Y + 1 + lam s| := by
    intro s
    have h := hroot s
    simp only [Set.mem_Ioo, not_and_or, not_lt] at h
    rcases h with h | h
    · rw [le_abs]; left; linarith
    · rw [le_abs]; right; linarith
  constructor
  · rw [← Finset.prod_div_distrib, Finset.abs_prod]
    calc ∏ s, |(Y + 1 + lam s) / (Y + lam s)| ≤ ∏ _s : Fin n, Real.exp (3 / (β - α)) := by
          apply Finset.prod_le_prod (fun s _ => abs_nonneg _)
          intro s _
          have h1 := key s
          have hpos : 0 < |Y + lam s| := by linarith
          have hne : Y + lam s ≠ 0 := abs_pos.mp hpos
          have e0 : (Y + 1 + lam s) / (Y + lam s) = 1 + 1 / (Y + lam s) := by field_simp; ring
          rw [e0]
          calc |1 + 1 / (Y + lam s)| ≤ 1 + 1/|Y + lam s| := by
                 have := abs_add_le (1:ℝ) (1 / (Y + lam s))
                 rw [abs_one, abs_div, abs_one] at this; exact this
            _ ≤ 1 + 3/(β-α) := by
                 have h2 : 1/|Y + lam s| ≤ 1/((β-α)/3) := one_div_le_one_div_of_le (by linarith) h1
                 have e : 1/((β-α)/3) = 3/(β-α) := by field_simp
                 linarith
            _ ≤ Real.exp (3/(β-α)) := by linarith [Real.add_one_le_exp (3/(β-α))]
      _ = Real.exp (3 * n / (β - α)) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]; congr 1; ring
  · rw [← Finset.prod_div_distrib, Finset.abs_prod]
    calc ∏ s, |(Y + lam s) / (Y + 1 + lam s)| ≤ ∏ _s : Fin n, Real.exp (4 / (β - α)) := by
          apply Finset.prod_le_prod (fun s _ => abs_nonneg _)
          intro s _
          have h1 := key2 s
          have hpos : 0 < |Y + 1 + lam s| := by linarith
          have hne : Y + 1 + lam s ≠ 0 := abs_pos.mp hpos
          have e0 : (Y + lam s) / (Y + 1 + lam s) = 1 + (-1) / (Y + 1 + lam s) := by field_simp; ring
          rw [e0]
          calc |1 + (-1) / (Y + 1 + lam s)| ≤ 1 + 1/|Y + 1 + lam s| := by
                 have := abs_add_le (1:ℝ) ((-1) / (Y + 1 + lam s))
                 rw [abs_one, abs_div, abs_neg, abs_one] at this; exact this
            _ ≤ 1 + 4/(β-α) := by
                 have h2 : 1/|Y + 1 + lam s| ≤ 1/((β-α)/4) := one_div_le_one_div_of_le (by linarith) h1
                 have e : 1/((β-α)/4) = 4/(β-α) := by field_simp
                 linarith
            _ ≤ Real.exp (4/(β-α)) := by linarith [Real.add_one_le_exp (4/(β-α))]
      _ = Real.exp (4 * n / (β - α)) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]; congr 1; ring

theorem bdd_add' {Λ : Type} {f g : Λ → ℂ} (hf : Bdd f) (hg : Bdd g) : Bdd (f + g) := by
  obtain ⟨a, ha⟩ := hf; obtain ⟨b, hb⟩ := hg
  exact ⟨a + b, fun x => (norm_add_le _ _).trans (add_le_add (ha x) (hb x))⟩

theorem bdd_smul' {Λ : Type} {f : Λ → ℂ} (c : ℂ) (hf : Bdd f) : Bdd (c • f) := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨‖c‖ * a, fun x => by
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (ha x) (norm_nonneg _)⟩

theorem bdd_zero' {Λ : Type} : Bdd (0 : Λ → ℂ) := ⟨0, fun x => by simp⟩

theorem bdd_sum' {Λ ι : Type} (T : Finset ι) (f : ι → Λ → ℂ) (hf : ∀ i, Bdd (f i)) :
    Bdd (∑ i ∈ T, f i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using bdd_zero'
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact bdd_add' (hf a) ih

theorem lim_sum' {Λ ι : Type} (LIM : (Λ → ℂ) → ℂ)
    (h1 : ∀ f g, Bdd f → Bdd g → LIM (f + g) = LIM f + LIM g)
    (h2 : ∀ (c : ℂ) f, Bdd f → LIM (c • f) = c * LIM f)
    (T : Finset ι) (f : ι → Λ → ℂ) (hf : ∀ i, Bdd (f i)) :
    LIM (∑ i ∈ T, f i) = ∑ i ∈ T, LIM (f i) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    have := h2 0 0 bdd_zero'
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, h1 _ _ (hf a) (bdd_sum' s f hf), ih]

theorem mpd : MeanPosDef := by
  intro Λ _ H _ _ LIM h1 h2 h3 h4 u B hu S c
  have hB : ∀ a b : Λ, Bdd (fun x => inner ℂ (u (x + a)) (u (x + b))) := fun a b =>
    ⟨B * B, fun x => (norm_inner_le_norm _ _).trans
      (mul_le_mul (hu _) (hu _) (norm_nonneg _) ((norm_nonneg _).trans (hu (x+a))))⟩
  have hB0 : ∀ b : Λ, Bdd (fun x => inner ℂ (u x) (u (x + b))) := fun b => by simpa using hB 0 b
  have e1 : ∀ σ σ' : Λ, LIM (fun x => inner ℂ (u x) (u (x + (σ - σ'))))
      = LIM (fun x => inner ℂ (u (x + σ')) (u (x + σ))) := by
    intro σ σ'
    rw [← h4 _ σ' (hB0 (σ - σ'))]
    congr 1; funext x; congr 2; abel
  have e2 : (∑ σ ∈ S, ∑ σ' ∈ S,
        LIM (fun x => inner ℂ (u x) (u (x + (σ - σ')))) * c σ * starRingEnd ℂ (c σ'))
      = LIM (∑ σ ∈ S, ∑ σ' ∈ S,
          (c σ * starRingEnd ℂ (c σ')) • (fun x => inner ℂ (u (x + σ')) (u (x + σ)))) := by
    rw [lim_sum' LIM h1 h2 S _ (fun σ => bdd_sum' S _ (fun σ' => bdd_smul' _ (hB σ' σ)))]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [lim_sum' LIM h1 h2 S _ (fun σ' => bdd_smul' _ (hB σ' σ))]
    refine Finset.sum_congr rfl fun σ' _ => ?_
    rw [h2 _ _ (hB σ' σ), e1]; ring
  rw [e2]
  apply h3
  · exact bdd_sum' S _ (fun σ => bdd_sum' S _ (fun σ' => bdd_smul' _ (hB σ' σ)))
  · intro x
    have key : (∑ σ ∈ S, ∑ σ' ∈ S,
          (c σ * starRingEnd ℂ (c σ')) • (fun x => inner ℂ (u (x + σ')) (u (x + σ)))) x
        = inner ℂ (∑ σ ∈ S, c σ • u (x + σ)) (∑ σ ∈ S, c σ • u (x + σ)) := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sum_inner, inner_sum,
        inner_smul_left, inner_smul_right]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [key]
    exact ⟨inner_self_nonneg (𝕜 := ℂ), inner_self_im (𝕜 := ℂ) _⟩

end Formalism.FourierDecayAlt.P.E2

theorem Formalism.FourierDecayAlt.P.middle_third_estimate : Formalism.FourierDecayAlt.E.MiddleThird := Formalism.FourierDecayAlt.P.E2.middleThird_ok
theorem Formalism.FourierDecayAlt.P.mean_matrix_posDef : Formalism.FourierDecayAlt.E.MeanPosDef := Formalism.FourierDecayAlt.P.E2.mpd
