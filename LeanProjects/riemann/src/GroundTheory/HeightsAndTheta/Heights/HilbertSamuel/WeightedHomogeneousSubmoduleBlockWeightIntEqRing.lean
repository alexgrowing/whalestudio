import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ProjectiveSpaceIncrementHyp
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

section Grading

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
  {M : Type*} [AddCommGroup M] [Module (MRing ι F) M] [Module F M]

theorem isMultigraded_iff_isMultigrading (ℳ : (K → ℤ) → Submodule F M) :
    IsMultigraded ι ℳ ↔ GroundTheory.Heights₂.Heights.HilbertSamuel.IsMultigrading ι M ℳ :=
  ⟨fun h => ⟨by convert h.internal, fun v m x hx => h.var_mul v m x hx⟩,
    fun h => ⟨by convert h.internal, fun v m x hx => h.smul_mem v m x hx⟩⟩

end Grading

section Multiplicity

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
  (M : Type*) [AddCommGroup M] [Module (MRing ι R) M]

end Multiplicity

section Cycle

variable {K : Type*} [Fintype K] [DecidableEq K] (ι : K → Type*) (F : Type*) [Field F]
  (M : Type*) [AddCommGroup M] [Module (MRing ι F) M]

end Cycle

section Examples

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

end Examples

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
