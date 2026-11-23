import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv

noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.SkewInt

open scoped Matrix.Norms.Operator in

theorem exp_entry_hasDerivAt {n : ℕ} (X : Mat n) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) : Mat n) i j)
      ((NormedSpace.exp (t • X) * X : Mat n) i j) t := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X t
  let L : Mat n →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  exact L.hasFDerivAt.comp_hasDerivAt t h

theorem exp_hasDerivAt {n : ℕ} (X : Mat n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) : Mat n)) (NormedSpace.exp (t • X) * X) t := by
  have : HasDerivAt (fun s : ℝ => (fun i j => (NormedSpace.exp (s • X) : Mat n) i j : Fin n → Fin n → ℂ))
      (fun i j => (NormedSpace.exp (t • X) * X : Mat n) i j) t := by
    rw [hasDerivAt_pi]
    intro i
    rw [hasDerivAt_pi]
    intro j
    exact exp_entry_hasDerivAt X t i j
  exact this

theorem curve_hasDerivAt {n : ℕ} (k X : Mat n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => k * (NormedSpace.exp (s • X) : Mat n)) (k * NormedSpace.exp (t • X) * X) t := by
  let L : Mat n →L[ℝ] Mat n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ k)
  have h := L.hasFDerivAt.comp_hasDerivAt t (exp_hasDerivAt X t)
  have e : L (NormedSpace.exp (t • X) * X) = k * NormedSpace.exp (t • X) * X := by
    rw [Matrix.mul_assoc]
    rfl
  exact h.congr_deriv e

theorem exp_mem_unitary {n : ℕ} {X : Mat n} (hX : Xᴴ = -X) (t : ℝ) :
    (NormedSpace.exp (t • X) : Mat n) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, ← Matrix.exp_conjTranspose, conjTranspose_smul,
    star_trivial, hX, smul_neg, Matrix.exp_neg]
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _))

theorem integral_Rd_skew : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ] [κ.IsMulRightInvariant] (u : Mat n → ℂ), ContDiffOn ℝ ∞ u (GLs n) → ∀ X : Mat n, Xᴴ = -X → ∫ k : Matrix.unitaryGroup (Fin n) ℂ, Rd X u k.1 ∂κ = 0 := by
  intro n _ _ κ _ _ u hu X hX
  haveI : CompactSpace (Matrix.unitaryGroup (Fin n) ℂ) := GlobalTheory.compactSpace_unitaryGroup (Fin n) ℂ
  haveI : SecondCountableTopology (Mat n) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix.unitaryGroup (Fin n) ℂ) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  let kt : ℝ → Matrix.unitaryGroup (Fin n) ℂ := fun t => ⟨NormedSpace.exp (t • X), exp_mem_unitary hX t⟩
  have hval : ∀ (y : Matrix.unitaryGroup (Fin n) ℂ) (t : ℝ),
      y.1 * (NormedSpace.exp (t • X) : Mat n) = (y * kt t).1 := fun _ _ => rfl
  have hcv : Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => k.1 := continuous_subtype_val
  have hRd := GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hu
  have cU : Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => u k.1 :=
    hu.continuousOn.comp_continuous hcv unit_mem
  have cR : Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => Rd X u k.1 :=
    hRd.continuousOn.comp_continuous hcv unit_mem
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn cR.continuousOn
  have key := GlobalTheory.CompanionTheory.RCalc.ByParts.integral_deriv_eq_zero (μ := κ) (V := ℂ)
    (F := fun t y => u (y.1 * (NormedSpace.exp (t • X) : Mat n)))
    (F' := fun t y => Rd X u (y.1 * (NormedSpace.exp (t • X) : Mat n)))
    (K := Set.univ) isCompact_univ (ε := 1) one_pos C ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa using key
  · intro t _
    simp only [hval]
    exact cU.comp (continuous_mul_right (kt t))
  · simp only [hval]
    exact cR.comp (continuous_mul_right (kt 0))
  · intro y t _
    have hg : y.1 * (NormedSpace.exp (t • X) : Mat n) ∈ GLs n := by
      rw [hval]
      exact unit_mem _
    have h := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hu hg).hasFDerivAt.comp_hasDerivAt t
      (curve_hasDerivAt y.1 X t)
    exact h
  · intro y hy
    exact absurd (Set.mem_univ y) hy
  · intro t _ y hy
    exact absurd (Set.mem_univ y) hy
  · intro t _ y _
    simp only [hval]
    exact hC _ (Set.mem_univ _)
  · intro t _
    simp only [hval]
    have h0 : kt 0 = 1 := by
      apply Subtype.ext
      simp [kt]
    rw [h0]
    simp only [mul_one]
    exact integral_mul_right_eq_self (fun y : Matrix.unitaryGroup (Fin n) ℂ => u y.1) (kt t)

end GlobalTheory.CompanionTheory.ModelS.SkewInt
