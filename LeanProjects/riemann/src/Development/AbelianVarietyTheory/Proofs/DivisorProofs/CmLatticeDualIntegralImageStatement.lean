import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeDualIntegralImage
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_lattice_dual_integral_image : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Φ : E →ₗ[ℚ] (Fin n → ℂ)) (L : Set E) (ρ : ℝ), ρ ≠ 0 →
    Submodule.span ℝ (Φ '' L) = ⊤ →
    (∀ x y : E, ∃ q : ℚ, (∑ j, (ρ : ℂ) * Φ x j * starRingEnd ℂ (Φ y j)).im = q) →
    ∀ w : Fin n → ℂ, (∀ x ∈ L, ∃ m : ℤ, (∑ j, (ρ : ℂ) * w j * starRingEnd ℂ (Φ x j)).im = m) → ∃ x : E, w = Φ x := by
  first | exact @GlobalTheory.CxDescent.mem_range_of_int_pairing | exact GlobalTheory.CxDescent.mem_range_of_int_pairing | (intros; apply GlobalTheory.CxDescent.mem_range_of_int_pairing <;> assumption)
