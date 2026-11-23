import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasseDerivativePowerSeriesMulSubstLeibniz
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffHasse
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasseDerivativePowerSeries_mul_subst_leibniz : ∀ (k : Type) [Field k] (a φ ψ : PowerSeries k) (l : ℕ), PowerSeries.constantCoeff a = 0 → ((GlobalTheory.PicDiv.hasse l (φ * ψ)).subst a : PowerSeries k) = ∑ p ∈ Finset.range (l + 1), ((GlobalTheory.PicDiv.hasse p φ).subst a : PowerSeries k) * (GlobalTheory.PicDiv.hasse (l - p) ψ).subst a := by
  first | exact @GlobalTheory.hasse_mul_subst | exact GlobalTheory.hasse_mul_subst | (intros; apply GlobalTheory.hasse_mul_subst <;> assumption)
