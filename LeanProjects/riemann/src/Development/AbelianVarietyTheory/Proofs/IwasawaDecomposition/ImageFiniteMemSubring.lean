import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory

theorem image_finite_mem_subring (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (iq : FractionRing O →+* Qbar l)
    (hiq : ∀ z : ℤ_[l], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) :
    ∃ T : Finset (Qbar l), ∀ R : Subring (Qbar l), (∀ z : ℤ_[l], algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) ∈ R) → (↑T ⊆ (R : Set (Qbar l))) → ∀ x : O, iq (algebraMap O (FractionRing O) x) ∈ R := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[l]) (M := O)
  refine ⟨s.image (fun x => iq (algebraMap O (FractionRing O) x)), ?_⟩
  intro R hR hT x
  have hx : x ∈ Submodule.span ℤ_[l] (s : Set O) := by rw [hs]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    exact hT (by simpa using Finset.mem_image_of_mem (fun x => iq (algebraMap O (FractionRing O) x)) hy)
  | zero => simpa using R.zero_mem
  | add a b _ _ ha hb => simpa using R.add_mem ha hb
  | smul c a _ ha =>
    rw [Algebra.smul_def, map_mul, map_mul, hiq]
    exact R.mul_mem (hR c) ha

end GlobalTheory
