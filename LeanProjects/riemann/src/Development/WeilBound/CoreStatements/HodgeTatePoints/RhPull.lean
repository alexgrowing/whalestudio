import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rh

theorem sub_pull : ∀ (p : ℕ) (C : Type) [Field C] (R : Type) [CommRing R] [Algebra R C] (N N' : Type) [AddCommGroup N] [AddCommGroup N'] (M : Submodule R (N → C)) (M' : Submodule R (N' → C)) (j : N →+ N') (K : AddSubgroup N), M'.map (LinearMap.funLeft R C (j : N → N')) = invFun M K → GenAF p M' ⊥ → GenAF p M K := by
  intro p C _ R _ _ N N' _ _ M M' j K hM hG g hg
  rw [← hM] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  have hinv : g' ∈ invFun M' ⊥ := ⟨hg', fun x k hk => by rw [AddSubgroup.mem_bot.1 hk, add_zero]⟩
  have h1 : g' ∈ Algebra.adjoin R ((afFun p (invFun M' ⊥) : Submodule R (N' → C)) : Set (N' → C)) :=
    hG hinv
  change (fun x => g' (j x)) ∈
    Algebra.adjoin R ((afFun p (invFun M K) : Submodule R (N → C)) : Set (N → C))
  clear hg' hinv
  induction h1 using Algebra.adjoin_induction with
  | mem f hf =>
    refine Algebra.subset_adjoin ⟨?_, fun x y => ?_⟩
    · rw [← hM]
      exact ⟨f, hf.1.1, rfl⟩
    · have := hf.2 (j x) (j y)
      simpa only [map_add] using this
  | algebraMap r => exact Subalgebra.algebraMap_mem _ r
  | add f f' _ _ h h' => exact Subalgebra.add_mem _ h h'
  | mul f f' _ _ h h' => exact Subalgebra.mul_mem _ h h'

end PositivityTheory.HtPt.Rh
