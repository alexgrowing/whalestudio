import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol

noncomputable section

namespace GlobalTheory.CompanionTheory.DualHol

theorem diag_eq_central_mul {F : Type} [Field F] (x y : Fˣ) : dg2 x y = dg2 y y * dg2 (x / y) 1 := by
  have hy : (y : F) ≠ 0 := y.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

theorem temperedBoundGL2_of_whittaker : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle) (μ₁ μ₂ : Fˣ →* ℂˣ) (V : Submodule ℂ (GL (Fin 2) F → ℂ)), IsUnit1 μ₁ → IsUnit1 μ₂ → WhittakerModelGL2 ψ μ₁ μ₂ V → ∀ W ∈ V, TemperedBoundGL2 W := by
  intro F _ _ _ _ _ _ ψ μ₁ μ₂ V h₁ h₂ H W hW
  obtain ⟨U, hU⟩ := H.smooth W hW
  have hWc : Continuous W := by
    refine IsLocallyConstant.continuous ?_
    rw [IsLocallyConstant.iff_exists_open]
    intro g
    refine ⟨{x | g⁻¹ * x ∈ U}, U.isOpen.preimage (continuous_const.mul continuous_id), by simp [U.one_mem],
      fun x hx => ?_⟩
    have := hU g _ hx
    simpa using this
  refine ⟨hWc.measurable, fun ε h0 _ => ?_⟩
  obtain ⟨C, B, hb⟩ := H.bound W hW ε h0
  refine ⟨C, B, fun x y k hk => ?_⟩
  have e : W (dg2 x y * k) = ((μ₁ y * μ₂ y : ℂˣ) : ℂ) * W (dg2 (x / y) 1 * k) := by
    rw [diag_eq_central_mul, mul_assoc, H.cen W hW]
  have hn : ‖((μ₁ y * μ₂ y : ℂˣ) : ℂ)‖ = 1 := by
    rw [Units.val_mul, norm_mul, h₁.2, h₂.2, one_mul]
  have hne : ((μ₁ y * μ₂ y : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  refine ⟨?_, fun hz => ?_⟩
  · rw [e, norm_mul, hn, one_mul]
    exact (hb (x / y) k hk).1
  · refine (hb (x / y) k hk).2 fun h0' => hz ?_
    rw [e, h0', mul_zero]

end GlobalTheory.CompanionTheory.DualHol
