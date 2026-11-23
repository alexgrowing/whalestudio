import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram

open Matrix Complex ComplexConjugate GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram
open scoped ComplexOrder ContDiff

namespace GlobalTheory

theorem isPosFrame_hodge_quot_and_sub : ∀ (ι : Type) [Fintype ι] (p q : ℕ) (U : Set (ι → ℂ))
    (ψ : (ι → ℂ) → Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ) (a b : ℝ),
    IsHodgeFrame U ψ → 0 < a → 0 < b →
      IsPosFrame U (fun x => (a : ℂ) • quotGram (ψ x)) ∧
        IsPosFrame U (fun x => (b : ℂ) • -subGram (ψ x)) := by
  intro ι _ p q U ψ a b h ha hb
  have hu : ∀ z ∈ U, IsUnit (subGram (ψ z)).det := fun z hz => by
    have h1 : IsUnit (subGram (ψ z)) := by simpa using (h.neg_sub z hz).isUnit.neg
    exact (Matrix.isUnit_iff_isUnit_det _).1 h1
  have ha' : (0 : ℂ) < (a : ℂ) := by exact_mod_cast ha
  have hb' : (0 : ℂ) < (b : ℂ) := by exact_mod_cast hb
  refine ⟨⟨h.isHermFrame.isOpen, fun i j z hz => ?_, fun z hz => (h.pos_quot z hz).smul ha'⟩,
    ⟨h.isHermFrame.isOpen, fun i j z hz => ?_, fun z hz => (h.neg_sub z hz).smul hb'⟩⟩
  · exact (MContDiffAt.smul (f := fun _ => (a : ℂ)) contDiffAt_const
      ((h.isHermFrame.mContDiffAt hz).quotGram (hu z hz)) i j).contDiffWithinAt
  · exact (MContDiffAt.smul (f := fun _ => (b : ℂ)) contDiffAt_const
      (h.isHermFrame.mContDiffAt hz).subGram.neg i j).contDiffWithinAt

end GlobalTheory
