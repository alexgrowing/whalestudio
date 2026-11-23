import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubleCosetMassEqRelIndexMulMass
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDcOfCover
open GlobalTheory.UnimodMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleCosetMass_eq_relIndex_mul_mass : ∀ (G : Type) [Group G] (Γ W K : Subgroup G), W ≤ K → Finite (GlobalTheory.UnimodMass.DC Γ W) → (∀ t : G, Finite {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}) → W.relIndex K ≠ 0 ∧ GlobalTheory.UnimodMass.mass Γ W = (W.relIndex K : ℚ) * GlobalTheory.UnimodMass.mass Γ K := by
  first | exact @GlobalTheory.UnimodMass.mass_eq_relIndex_mul | exact GlobalTheory.UnimodMass.mass_eq_relIndex_mul | (intros; apply GlobalTheory.UnimodMass.mass_eq_relIndex_mul <;> assumption)
