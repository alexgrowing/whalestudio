import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationModuleUnitDual
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_module_unit_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule (OF E) E),
    (∃ N : ℕ, 0 < N ∧ (∀ x : 𝓞 E, (N : E) * algebraMap (𝓞 E) E x ∈ L) ∧ ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) →
    IsUnit (polMod L) ∧ polMod L * L = dualLat L := by
  first | exact @GlobalTheory.PolModLattice.polMod_isUnit_mul_eq_dual | exact GlobalTheory.PolModLattice.polMod_isUnit_mul_eq_dual | (intros; apply GlobalTheory.PolModLattice.polMod_isUnit_mul_eq_dual <;> assumption)
