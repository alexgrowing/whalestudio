import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedDoublingSumGLConvergentLValue
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_doubling_sum_GL_convergent_L_value : GlobalTheory.Published.UnramifiedDoublingGL →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (N : ℕ) [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)]
    (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure], μK (KO k (Fin N)) = 1 →
  ∀ (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
  ∀ (α : Fin N → ℂˣ) (ρ : ℝ), (∀ x, ‖(α x : ℂ)‖ ≤ (resCard k : ℝ) ^ ρ ∧ ‖(α x : ℂ)‖⁻¹ ≤ (resCard k : ℝ) ^ ρ) →
  ∀ ψ : GL (Fin N) k → ℂ, IsBorelSph k (borelParam (resCard k) α) ψ →
  ∀ s : ℂ, ρ - 1 / 2 < s.re →
    Summable (fun e : {e : Fin N → ℤ // Antitone e} => ‖(μK.real (cell k (Fin N) ϖ e) : ℂ) *
      ((resCard k : ℂ) ^ (-((N : ℂ) / 2 + s) * (sumAbs e.1 : ℂ)) * zonalInt μK ψ (torusElt k (Fin N) ϖ e))‖) ∧
    HasSum (fun e : {e : Fin N → ℤ // Antitone e} => (μK.real (cell k (Fin N) ϖ e) : ℂ) *
      ((resCard k : ℂ) ^ (-((N : ℂ) / 2 + s) * (sumAbs e.1 : ℂ)) * zonalInt μK ψ (torusElt k (Fin N) ϖ e)))
      (lFactor (resCard k) α (s + 1 / 2) * lFactor (resCard k) α⁻¹ (s + 1 / 2) * invNormFactor (resCard k) N s) := by
  first | exact @GlobalTheory.DoublingSeries.unramified_doubling_sum | exact GlobalTheory.DoublingSeries.unramified_doubling_sum | (intros; apply GlobalTheory.DoublingSeries.unramified_doubling_sum <;> assumption)
