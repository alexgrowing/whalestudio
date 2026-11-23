import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.UnitPreserving

open NumberField
open scoped nonZeroDivisors ENNReal Classical

noncomputable section

namespace PI.Residue

def idealEquiv (K : Type) [Field K] [NumberField K] :
    (Ideal (𝓞 K))⁰ ≃ {I : Ideal (𝓞 K) // I ≠ ⊥} :=
  Equiv.subtypeEquivRight fun I => by rw [mem_nonZeroDivisors_iff_ne_zero, Ideal.zero_eq_bot]

theorem classSum : ClassSum := by
  intro K _ _ s hs
  have h1 : ∑ C : ClassGroup (𝓞 K), classZeta K C s =
      ∑' I : (Ideal (𝓞 K))⁰, ENNReal.ofReal ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ (-s)) := by
    rw [← (Equiv.sigmaFiberEquiv (fun I : (Ideal (𝓞 K))⁰ => ClassGroup.mk0 I)).tsum_eq,
      ENNReal.tsum_sigma', tsum_fintype]
    rfl
  rw [h1, idealZeta, ENNReal.ofReal_tsum_of_nonneg (fun I => by positivity) hs,
    ← (idealEquiv K).tsum_eq]
  exact le_of_eq rfl

end PI.Residue
