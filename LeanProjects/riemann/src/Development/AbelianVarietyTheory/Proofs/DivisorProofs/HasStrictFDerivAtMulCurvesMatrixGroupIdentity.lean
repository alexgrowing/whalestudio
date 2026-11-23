import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhaseFrame
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

theorem GlobalTheory.hasStrictFDerivAt_mul_curves_at_identity : ∀ (ι : Type) [Fintype ι] (r : ℕ) (H : Subgroup (ι → GL (Fin r) ℂ)) (W₁ W₂ : Type) [NormedAddCommGroup W₁] [NormedSpace ℝ W₁] [NormedAddCommGroup W₂] [NormedSpace ℝ W₂] (σ : W₁ → H) (t : W₂ → H) (D₁ : W₁ →L[ℝ] (ι → Fin r → Fin r → ℂ)) (D₂ : W₂ →L[ℝ] (ι → Fin r → Fin r → ℂ)), σ 0 = 1 → t 0 = 1 → HasStrictFDerivAt (fun w => fun τ i j => ((((σ w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) D₁ 0 → HasStrictFDerivAt (fun w => fun τ i j => ((((t w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) D₂ 0 → HasStrictFDerivAt (fun w : W₁ × W₂ => fun τ i j => ((((σ w.1 * t w.2 : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) (D₁.comp (ContinuousLinearMap.fst ℝ W₁ W₂) + D₂.comp (ContinuousLinearMap.snd ℝ W₁ W₂)) 0 := by
  intro ι _ r H W₁ W₂ _ _ _ _ σ t D₁ D₂ hσ ht h₁ h₂
  set f₁ : W₁ → ι → Fin r → Fin r → ℂ := fun w τ i j =>
    ((((σ w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j with hf₁
  set f₂ : W₂ → ι → Fin r → Fin r → ℂ := fun w τ i j =>
    ((((t w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j with hf₂
  have e : (fun w : W₁ × W₂ => fun τ i j =>
      ((((σ w.1 * t w.2 : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) =
      fun w τ i j => ∑ c, f₁ w.1 τ i c * f₂ w.2 τ c j := by
    funext w τ i j
    simp [hf₁, hf₂, Matrix.mul_apply]
  have z₁ : ∀ τ i c, f₁ 0 τ i c = (1 : Matrix (Fin r) (Fin r) ℂ) i c := by
    intro τ i c; simp [hf₁, hσ]
  have z₂ : ∀ τ c j, f₂ 0 τ c j = (1 : Matrix (Fin r) (Fin r) ℂ) c j := by
    intro τ c j; simp [hf₂, ht]
  have g₁ : HasStrictFDerivAt (fun w : W₁ × W₂ => f₁ w.1)
      (D₁.comp (ContinuousLinearMap.fst ℝ W₁ W₂)) (0 : W₁ × W₂) :=
    h₁.comp (0 : W₁ × W₂) (hasStrictFDerivAt_fst (p := (0 : W₁ × W₂)))
  have g₂ : HasStrictFDerivAt (fun w : W₁ × W₂ => f₂ w.2)
      (D₂.comp (ContinuousLinearMap.snd ℝ W₁ W₂)) (0 : W₁ × W₂) :=
    h₂.comp (0 : W₁ × W₂) (hasStrictFDerivAt_snd (p := (0 : W₁ × W₂)))
  rw [e]
  refine hasStrictFDerivAt_pi'.2 fun τ => hasStrictFDerivAt_pi'.2 fun i =>
    hasStrictFDerivAt_pi'.2 fun j => ?_
  have a₁ : ∀ c, HasStrictFDerivAt (fun w : W₁ × W₂ => f₁ w.1 τ i c)
      ((ContinuousLinearMap.proj c).comp ((ContinuousLinearMap.proj i).comp
        ((ContinuousLinearMap.proj τ).comp (D₁.comp (ContinuousLinearMap.fst ℝ W₁ W₂))))) 0 :=
    fun c => hasStrictFDerivAt_pi'.1 (hasStrictFDerivAt_pi'.1 (hasStrictFDerivAt_pi'.1 g₁ τ) i) c
  have a₂ : ∀ c, HasStrictFDerivAt (fun w : W₁ × W₂ => f₂ w.2 τ c j)
      ((ContinuousLinearMap.proj j).comp ((ContinuousLinearMap.proj c).comp
        ((ContinuousLinearMap.proj τ).comp (D₂.comp (ContinuousLinearMap.snd ℝ W₁ W₂))))) 0 :=
    fun c => hasStrictFDerivAt_pi'.1 (hasStrictFDerivAt_pi'.1 (hasStrictFDerivAt_pi'.1 g₂ τ) c) j
  have hs0 := HasStrictFDerivAt.sum (u := Finset.univ) (A := fun c (w : W₁ × W₂) => f₁ w.1 τ i c * f₂ w.2 τ c j)
    (fun c _ => (a₁ c).mul (a₂ c))
  have ef : (fun w : W₁ × W₂ => ∑ c, f₁ w.1 τ i c * f₂ w.2 τ c j) =
      ∑ c, (fun (w : W₁ × W₂) => f₁ w.1 τ i c * f₂ w.2 τ c j) := by
    funext w
    simp [Finset.sum_apply]
  rw [ef]
  refine hs0.congr_fderiv ?_
  clear ef hs0 a₁ a₂ g₁ g₂ e
  clear_value f₁ f₂
  clear hf₁ hf₂ h₁ h₂ hσ ht σ t
  refine ContinuousLinearMap.ext fun w => ?_
  simp [z₁, z₂, Matrix.one_apply, Finset.sum_add_distrib, ite_mul]
  ring
