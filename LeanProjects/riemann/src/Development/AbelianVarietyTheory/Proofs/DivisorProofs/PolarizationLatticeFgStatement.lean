import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationLatticeFg
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_lattice_fg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule (OF E) E),
    (∃ N : ℕ, 0 < N ∧ ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) → IsUnit (polMod L) → (polMod L * L).toAddSubgroup.FG := by
  first | exact @GlobalTheory.polMod_mul_fg | exact GlobalTheory.polMod_mul_fg | (intros; apply GlobalTheory.polMod_mul_fg <;> assumption)
