import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SubClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SeqComplexExactAtOfAllLinksExactAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExactAtLinkInSplitSeqOfExactAtSplitSeq
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsSplitSeqLinkInOrthogonalEqLinkIn
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SubClosedSplitSeqAndUniSeqWithMemIff

open GlobalTheory.SeqCx Matrix UpperTheory.V.KL

namespace GlobalTheory.SeqCx

theorem exactAt_split_kill_uni : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ n : ℕ,
    (∀ n' < n, ∀ p' : ℕ, 2 * p' + s + 1 ≤ n' → ExactAt (splitSeq R n') p') →
    ∀ (a : ℕ) (w : List (Fin n → R)), w ∈ uniSeq R n → 1 ≤ w.length →
    2 * a + w.length + s + 1 ≤ n →
    ExactAt {σ | σ ∈ splitSeq R n ∧ ∀ y ∈ σ, ∀ u ∈ w, y.2 ⬝ᵥ u = 0} a := by
  intro R _ s hs n hind a w hw hw1 hlen
  obtain ⟨hsubS, -, -, huni⟩ := T.subClosed_splitSeq_and_uniSeq_with_mem_iff R n
  obtain ⟨γ, hγ, hγw⟩ := (huni w).mp hw
  subst hγw
  rw [List.length_map] at hw1 hlen
  have hF : {σ : List ((Fin n → R) × (Fin n → R)) |
      σ ∈ splitSeq R n ∧ ∀ y ∈ σ, ∀ u ∈ List.map Prod.fst γ, y.2 ⬝ᵥ u = 0} =
      {x | x ∈ splitSeq R n ∧ ∀ y ∈ x, ∀ z ∈ γ, y.2 ⬝ᵥ z.1 = 0} := by
    ext σ
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun y hy z hz => h2 y hy z.1 (List.mem_map.mpr ⟨z, hz, rfl⟩)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun y hy u hu => ?_⟩
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hu
      exact h2 y hy z hz
  rw [hF]
  refine T.seqComplex_exactAt_of_all_links_exactAt _ _ {y : (Fin n → R) × (Fin n → R) | ∀ z ∈ γ, z.2 ⬝ᵥ y.1 = 0} ?_ a ?_
  · intro l hl l' hl'
    exact ⟨hsubS l hl.1 l' hl', fun y hy z hz => hl.2 y (hl'.subset hy) z hz⟩
  · intro σ hσ hσlen
    obtain ⟨ρ, hρ, hρlen, hlink⟩ := T.exists_splitSeq_linkIn_orthogonal_eq_linkIn R n γ σ hγ hσ.1 hσ.2
    rw [hlink]
    exact T.exactAt_linkIn_splitSeq_of_exactAt_splitSeq R s hs n (n - ρ.length) (a - σ.length) ρ hρ (by omega) (by omega)
      (hind (n - ρ.length) (by omega) (a - σ.length) (by omega))

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL
theorem _root_.GlobalTheory.T.splitSeq_forms_kill_uniSeq_exactAt : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ n : ℕ, (∀ n' < n, ∀ p' : ℕ, 2 * p' + s + 1 ≤ n' → ExactAt (splitSeq R n') p') → ∀ (a : ℕ) (w : List (Fin n → R)), w ∈ uniSeq R n → 1 ≤ w.length → 2 * a + w.length + s + 1 ≤ n → ExactAt {σ | σ ∈ splitSeq R n ∧ ∀ y ∈ σ, ∀ u ∈ w, y.2 ⬝ᵥ u = 0} a := by
  first
  | exact @GlobalTheory.SeqCx.exactAt_split_kill_uni
end
