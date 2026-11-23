import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalUnramifiedIntegralValue
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)
open Formalism.UG (IsUnifV qV)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_unramified_integral_value : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (n : ℕ) (s : ℂ), (n : ℝ) / 2 < s.re → ∀ (z : ℂˣ) (φ : GL (Fin n) (Fv F v) → ℂ), ‖(z : ℂ)‖ = 1 →
    (∀ (ϖ : (Fv F v)ˣ), IsUnifV F v ϖ.1 → ∀ (e : Fin n → ℤ) (T : GL (Fin n) (Fv F v)), T.1 = Matrix.diagonal (fun i => ϖ.1 ^ e i) → ∀ k₁ ∈ KGL v n, ∀ k₂ ∈ KGL v n, φ (k₁ * T * k₂) = (z : ℂ) ^ (∑ i, e i) * (qV F v : ℂ) ^ (-((n : ℂ) / 2 + s) * ((∑ i, |e i| : ℤ) : ℂ))) →
    (∀ g, ∀ k ∈ KGL v n, φ (g * k) = φ g) ∧
    HasSum (fun a : GL (Fin n) (Fv F v) ⧸ KGL v n => φ a.out)
      ((∏ j ∈ Finset.range n, (1 - (z : ℂ) * (qV F v : ℂ) ^ (-(s + (n : ℂ) / 2 - (j : ℂ))))⁻¹ * (1 - (z : ℂ)⁻¹ * (qV F v : ℂ) ^ (-(s + (n : ℂ) / 2 - (j : ℂ))))⁻¹) *
        ∏ j ∈ Finset.Icc 1 n, (1 - (qV F v : ℂ) ^ (-(2 * s + (j : ℂ))))) := by
  first | exact @GlobalTheory.ZetaGL.zeta_sum_GL_trivial | exact GlobalTheory.ZetaGL.zeta_sum_GL_trivial | (intros; apply GlobalTheory.ZetaGL.zeta_sum_GL_trivial <;> assumption)
