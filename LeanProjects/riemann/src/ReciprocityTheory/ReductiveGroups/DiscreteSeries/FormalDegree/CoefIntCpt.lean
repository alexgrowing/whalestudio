import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IntegrableOfDecayVG
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IntegrVGA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CoefOp

noncomputable section

open Finset MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool}

theorem coefIntCpt_toE_continuous (n : ℕ) :
    Continuous (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) := by
  exact (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional

theorem coefIntCpt_unitary (hq : S7.q0 ε = 0) (g : S7.UJ ε) :
    (S7.toM g)ᴴ * S7.toM g = 1 := by
  have h1 : inUJ ε (S7.toM g) := g.2
  unfold inUJ at h1
  unfold S7.q0 pOf qOf at hq
  rcases Nat.min_eq_zero_iff.mp hq with h0 | h0
  · have hf : ∀ a, ε a = false := fun a => by
      simpa using Finset.filter_eq_empty_iff.mp (Finset.card_eq_zero.mp h0) (Finset.mem_univ a)
    have hJ : Jm ε = -1 := by
      ext i j
      by_cases h : i = j <;> simp [Jm, Matrix.diagonal_apply, Matrix.one_apply, h, hf]
    rw [hJ] at h1
    simpa using h1
  · have hf : ∀ a, ε a = true := fun a => by
      simpa using Finset.filter_eq_empty_iff.mp (Finset.card_eq_zero.mp h0) (Finset.mem_univ a)
    have hJ : Jm ε = 1 := by
      ext i j
      by_cases h : i = j <;> simp [Jm, Matrix.diagonal_apply, Matrix.one_apply, h, hf]
    rw [hJ] at h1
    simpa using h1

theorem coefIntCpt_hs (hq : S7.q0 ε = 0) (g : S7.UJ ε) : S7.hs (S7.toM g) = n := by
  have hu := coefIntCpt_unitary hq g
  unfold S7.hs
  have hcol : ∀ j, ∑ i, ‖S7.toM g i j‖ ^ 2 = 1 := by
    intro j
    have h := congrFun (congrFun hu j) j
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
    simp only [Matrix.conjTranspose_apply] at h
    have h' : ((∑ i, ‖S7.toM g i j‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← h]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Complex.conj_mul']
      rfl
    exact_mod_cast h'
  rw [Finset.sum_comm]
  simp [hcol]

theorem integrable_opPow_of_compact (hq : S7.q0 ε = 0) (Ψ : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hcont : ContinuousOn Ψ {g | inUJ ε g}) (hle : ∀ g, inUJ ε g → ‖Ψ g‖ ≤ 1)
    {N : ℝ} (hN : 0 ≤ N) (ν : Measure (S7.UJ ε)) [ν.IsHaarMeasure] :
    Integrable (fun g : S7.UJ ε =>
      ‖Ψ (S7.toM g)‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (S7.toM g)‖ ^ N) ν := by
  obtain ⟨s, hsc⟩ := S7.exists_signVG ε
  have hfc : Continuous (fun g : S7.UJ ε =>
      ‖Ψ (S7.toM g)‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (S7.toM g)‖ ^ N) := by
    have h1 : Continuous fun g : S7.UJ ε => Ψ (S7.toM g) :=
      hcont.comp_continuous (S7.continuous_toM ε) (fun g => g.2)
    have h2 : Continuous fun g : S7.UJ ε => Matrix.toEuclideanCLM (𝕜 := ℂ) (S7.toM g) :=
      (coefIntCpt_toE_continuous n).comp (S7.continuous_toM ε)
    exact h1.norm.mul (h2.norm.rpow_const fun _ => Or.inr hN)
  refine S7.integrable_of_decayVG ε s ν _ hfc.aestronglyMeasurable (Real.sqrt n ^ N)
    (fun g _ => ?_) 1 ?_ (fun g hg => ?_)
  · have hop := coefOp_le_sqrt_hs (S7.toM g)
    rw [coefIntCpt_hs hq g] at hop
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc _ ≤ 1 * Real.sqrt n ^ N :=
          mul_le_mul (hle _ g.2) (Real.rpow_le_rpow (norm_nonneg _) hop hN) (by positivity) zero_le_one
      _ = _ := one_mul _
  · rw [hsc, hq]; norm_num
  · exfalso
    rw [coefIntCpt_hs hq g] at hg
    have e1 : (1 : ℝ) ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
    have e0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith

end ReciprocityTheory.ChartRestriction.DS
