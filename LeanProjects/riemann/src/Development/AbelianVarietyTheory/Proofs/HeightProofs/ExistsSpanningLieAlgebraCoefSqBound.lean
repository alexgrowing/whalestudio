import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContDiffMatrixRightInvariantDerivative
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

namespace GlobalTheory.KGap

theorem entry_sq_le_hs {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖Y i j‖ ^ 2 ≤ Formalism.REAL.hs Y := by
  unfold Formalism.REAL.hs
  calc ‖Y i j‖ ^ 2 ≤ ∑ j', ‖Y i j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ‖Y i j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖Y i' j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖Y i' j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)

theorem hs_nonneg' {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ Formalism.REAL.hs Y := by
  unfold Formalism.REAL.hs; positivity

theorem sup_norm_sq_le_hs {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) :
    ‖(Matrix.of.symm Y : Fin n → Fin n → ℂ)‖ ^ 2 ≤ Formalism.REAL.hs Y := by
  have h : ‖(Matrix.of.symm Y : Fin n → Fin n → ℂ)‖ ≤ Real.sqrt (Formalism.REAL.hs Y) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
    exact Real.le_sqrt_of_sq_le (entry_sq_le_hs Y i j)
  calc ‖(Matrix.of.symm Y : Fin n → Fin n → ℂ)‖ ^ 2 ≤ Real.sqrt (Formalism.REAL.hs Y) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = Formalism.REAL.hs Y := Real.sq_sqrt (hs_nonneg' Y)

theorem spanning_coef_bound : ∀ {n : ℕ} (ε : Fin n → Bool) {r : ℕ} (X : Fin r → Mx n), (∀ Y, inK ε Y → ∃ c : Fin r → ℝ, Y = ∑ j, (c j : ℂ) • X j) → ∃ C : ℝ, 0 ≤ C ∧ ∀ Y, inK ε Y → ∃ c : Fin r → ℝ, Y = ∑ j, (c j : ℂ) • X j ∧ ∑ j, c j ^ 2 ≤ C * Formalism.REAL.hs Y := by
  intro n ε r X hX
  let Tm : (Fin r → ℝ) →ₗ[ℝ] (Fin n → Fin n → ℂ) :=
    { toFun := fun c => Matrix.of.symm (∑ j, (c j : ℂ) • X j)
      map_add' := by
        intro a b; funext i k
        simp [add_smul, Finset.sum_add_distrib, Matrix.sum_apply]
      map_smul' := by
        intro t a; funext i k
        simp [Matrix.sum_apply, Finset.mul_sum, mul_assoc] }
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective Tm.rangeRestrict (LinearMap.range_rangeRestrict Tm)
  obtain ⟨P, hP⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.range Tm).subtype (Submodule.ker_subtype _)
  let L : (Fin n → Fin n → ℂ) →ₗ[ℝ] (Fin r → ℝ) := g ∘ₗ P
  let Lc := LinearMap.toContinuousLinearMap L
  refine ⟨r * ‖Lc‖ ^ 2, by positivity, ?_⟩
  intro Y hY
  obtain ⟨c0, hc0⟩ := hX Y hY
  have hYW : Matrix.of.symm Y ∈ LinearMap.range Tm := ⟨c0, by simp [Tm, hc0]⟩
  have hPY : P (Matrix.of.symm Y) = ⟨_, hYW⟩ := by
    have := LinearMap.congr_fun hP ⟨_, hYW⟩
    simpa using this
  refine ⟨L (Matrix.of.symm Y), ?_, ?_⟩
  · have h1 := LinearMap.congr_fun hg (P (Matrix.of.symm Y))
    have h2 : Tm (L (Matrix.of.symm Y)) = Matrix.of.symm Y := by
      have := congrArg Subtype.val h1
      simpa [L, hPY] using this
    have h3 := congrArg Matrix.of h2
    simpa [Tm] using h3.symm
  · set v := Matrix.of.symm Y with hv
    have hb : ∀ j, (L v) j ^ 2 ≤ ‖Lc‖ ^ 2 * ‖v‖ ^ 2 := by
      intro j
      have h1 : ‖(L v) j‖ ≤ ‖L v‖ := norm_le_pi_norm (L v) j
      have h2 : ‖L v‖ ≤ ‖Lc‖ * ‖v‖ := Lc.le_opNorm v
      have h3 : |(L v) j| ≤ ‖Lc‖ * ‖v‖ := by
        rw [← Real.norm_eq_abs]; exact h1.trans h2
      rw [← mul_pow]
      exact sq_le_sq' (by linarith [abs_le.mp h3]) (abs_le.mp h3).2
    have hv2 : ‖v‖ ^ 2 ≤ Formalism.REAL.hs Y := sup_norm_sq_le_hs Y
    calc ∑ j, (L v) j ^ 2 ≤ ∑ _j : Fin r, ‖Lc‖ ^ 2 * ‖v‖ ^ 2 := Finset.sum_le_sum fun j _ => hb j
      _ = r * ‖Lc‖ ^ 2 * ‖v‖ ^ 2 := by simp; ring
      _ ≤ r * ‖Lc‖ ^ 2 * Formalism.REAL.hs Y := by gcongr

end GlobalTheory.KGap
