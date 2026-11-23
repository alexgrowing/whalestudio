import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExactAtLinkSuccUnionTranslateOfCoordOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsAutomorphismPreservingTranslatesCoordOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExactAtLinkInUniMOfExactAtMapLinearEquiv

open GlobalTheory.SeqCx Matrix UpperTheory.V.KL

namespace GlobalTheory

theorem uniM_map_equiv {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (ψ : M ≃ₗ[R] M)
    {τ : List M} (hτ : τ ∈ uniM R M) : τ.map ψ ∈ uniM R M := by
  exact ((T.subClosed_and_perm_and_linearEquiv_invariant_uniM R M).2.2 ψ τ).mpr hτ

theorem linkExact_low_union_aff_of_ne_nil : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ n : ℕ, s ≤ n →
    LinkExactAff R s n → ∀ j : ℕ, n + 1 ≤ j → ∀ τ ∈ uniM R (ℕ →₀ R), τ ≠ [] → ∀ p : ℕ,
    p + s + τ.length ≤ n + 2 →
    ExactAt (linkIn (uniM R (ℕ →₀ R)) (low R (n + 1) ∪ aff R (n + 1) j) τ) p := by
  intro R _ s hs n hn hL j hj τ hτ hne p hp
  obtain ⟨v, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hv : [v] ∈ uniM R (ℕ →₀ R) := (T.subClosed_and_perm_and_linearEquiv_invariant_uniM R (ℕ →₀ R)).1 _ hτ [v] (by simp)
  obtain ⟨ψ, hlow, haff, hψv⟩ := T.exists_automorphism_preserving_translates_coord_one R s hs n hn v hv
  refine T.exactAt_linkIn_uniM_of_exactAt_map_linearEquiv R (ℕ →₀ R) ψ (low R (n + 1) ∪ aff R (n + 1) j) ?_ _ p ?_
  · intro x
    simp only [Set.mem_union, hlow, haff]
  · refine T.exactAt_link_succ_union_translate_of_coord_one R s n hL j hj _ (uniM_map_equiv ψ hτ) (ψ v) (by simp) hψv p ?_
    simpa using hp

end GlobalTheory

section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL
theorem _root_.GlobalTheory.T.exactAt_linkIn_succ_union_translate_of_ne_nil : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ n : ℕ, s ≤ n → LinkExactAff R s n → ∀ j : ℕ, n + 1 ≤ j → ∀ τ ∈ uniM R (ℕ →₀ R), τ ≠ [] → ∀ p : ℕ, p + s + τ.length ≤ n + 2 → ExactAt (linkIn (uniM R (ℕ →₀ R)) (low R (n + 1) ∪ aff R (n + 1) j) τ) p := by
  first
  | exact @GlobalTheory.linkExact_low_union_aff_of_ne_nil
  | exact @GlobalTheory.uniM_map_equiv
end
