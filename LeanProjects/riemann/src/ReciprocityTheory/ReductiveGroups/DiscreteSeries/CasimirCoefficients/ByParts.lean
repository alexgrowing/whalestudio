import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem kByParts {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (ε : Fin n → Bool) (F D : KG ε → E) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) (γ : ℝ → KG ε)
    (hγ : ∀ t, toMK (γ t) = NormedSpace.exp ((t : ℂ) • Z)) (hF : Continuous F) (hD : Continuous D)
    (hder : ∀ k, HasDerivAt (fun t => F (k * γ t)) (D k) 0) :
    ∫ k, D k ∂(muK ε) = 0 := by
  haveI := muK_rightInvariant ε
  haveI := compactSpace_KG ε
  obtain ⟨γ', -, hγ', hadd'⟩ := exists_oneParam ε hZ
  have hinj : ∀ a b : KG ε, toMK a = toMK b → a = b := by
    intro a b h
    exact Subtype.ext (Subtype.ext (Units.ext h))
  have hγγ : ∀ t, γ t = γ' t := fun t => hinj _ _ (by rw [hγ, hγ'])
  have hadd : ∀ s t, γ (s + t) = γ s * γ t := by
    intro s t
    rw [hγγ, hγγ, hγγ, hadd']
  have h0 : γ 0 = 1 := by
    have h00 := hadd 0 0
    rw [add_zero] at h00
    exact mul_left_cancel (a := γ 0) (by rw [mul_one]; exact h00.symm)

  have hderiv : ∀ k t, HasDerivAt (fun u => F (k * γ u)) (D (k * γ t)) t := by
    intro k t
    have h1 := hder (k * γ t)
    have h2 : (fun s => F (k * γ t * γ s)) = fun s => F (k * γ (t + s)) := by
      funext s
      rw [hadd, mul_assoc]
    rw [h2] at h1
    have h3 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h1)
    have h4 : (fun x => F (k * γ (t + (x - t)))) = fun u => F (k * γ u) := by
      funext x
      rw [show t + (x - t) = x by ring]
    rw [h4] at h3
    exact h3
  obtain ⟨C, hC⟩ : ∃ C, ∀ k, ‖D k‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_range hD.norm).bddAbove
    exact ⟨C, fun k => hC ⟨k, rfl⟩⟩
  have hFm : ∀ t, Continuous fun k : KG ε => F (k * γ t) := fun t =>
    hF.comp (continuous_mul_right _)
  have hDm : Continuous fun k : KG ε => D (k * γ 0) := hD.comp (continuous_mul_right _)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := muK ε)
    (F := fun t k => F (k * γ t)) (F' := fun t k => D (k * γ t)) (x₀ := (0 : ℝ))
    (bound := fun _ => C) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun t =>
      ((hFm t).stronglyMeasurable_of_hasCompactSupport (isClosed_tsupport _).isCompact).aestronglyMeasurable)
    ((hFm 0).integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact)
    ((hDm.stronglyMeasurable_of_hasCompactSupport (isClosed_tsupport _).isCompact).aestronglyMeasurable)
    (ae_of_all _ fun k t _ => hC _) (integrable_const C)
    (ae_of_all _ fun k t _ => hderiv k t)
  have key2 : HasDerivAt (fun t => ∫ k, F (k * γ t) ∂(muK ε)) (∫ k, D (k * γ 0) ∂(muK ε)) 0 :=
    key.2
  have hconst : (fun t => ∫ k, F (k * γ t) ∂(muK ε)) = fun _ => ∫ k, F k ∂(muK ε) := by
    funext t
    exact integral_mul_right_eq_self (fun k => F k) (γ t)
  rw [hconst] at key2
  have huniq := key2.unique (hasDerivAt_const (0 : ℝ) (∫ k, F k ∂(muK ε)))
  simpa [h0] using huniq

end ReciprocityTheory.ChartRestriction.DS.S7
