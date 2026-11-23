import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SubClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SubClosedSplitSeqAndUniSeqWithMemIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SeqChainCycleBoundedByCone
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsSplitSeqLinkInOrthogonalEqLinkIn
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExactAtLinkInSplitSeqOfExactAtSplitSeq
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsHomologousCycleWithEntriesInOfExactAtLinks

open GlobalTheory.SeqCx Matrix UpperTheory.V.KL

namespace GlobalTheory.SeqCx

theorem cycle_formsKill_bound_splitSeq : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ n : ℕ, (∀ n' < n, ∀ p' : ℕ, 2 * p' + s + 1 ≤ n' → ExactAt (splitSeq R n') p') → ∀ (p : ℕ) (u : Fin n → R), [u] ∈ uniSeq R n → 2 * p + s + 1 ≤ n → ∀ c ∈ chains {σ | σ ∈ splitSeq R n ∧ ∀ y ∈ σ, ∀ v ∈ [u], y.2 ⬝ᵥ v = 0} p, bd _ c = 0 → ∃ b ∈ chains (splitSeq R n) (p + 1), bd _ b = c := by
  intro R _ s hs n hlow p u hu hpn c hc hcz
  obtain ⟨f, hf⟩ := hu
  obtain ⟨w, hwu⟩ : ∃ w : Fin n → R, w ⬝ᵥ u = 1 := ⟨_, by simpa using hf ⟨0, by simp⟩ ⟨0, by simp⟩⟩
  obtain ⟨hsc, -, hchar, -⟩ := GlobalTheory.T.subClosed_splitSeq_and_uniSeq_with_mem_iff R n
  have hγF : [(u, w)] ∈ splitSeq R n := by
    rw [hchar]
    simp [hwu]
  have hGeq : {σ | σ ∈ splitSeq R n ∧ ∀ y ∈ σ, ∀ v ∈ [u], y.2 ⬝ᵥ v = 0} =
      {x | x ∈ splitSeq R n ∧ ∀ y ∈ x, ∀ z ∈ [(u, w)], y.2 ⬝ᵥ z.1 = 0} := by
    ext σ
    simp
  rw [hGeq] at hc
  have hG'sc : SubClosed {x | x ∈ splitSeq R n ∧ ∀ y ∈ x, ∀ z ∈ [(u, w)], y.2 ⬝ᵥ z.1 = 0} := by
    intro l hl l' hl'
    exact ⟨hsc l hl.1 l' hl', fun y hy => hl.2 y (hl'.subset hy)⟩
  have hlinks : ∀ τ ∈ {x | x ∈ splitSeq R n ∧ ∀ y ∈ x, ∀ z ∈ [(u, w)], y.2 ⬝ᵥ z.1 = 0},
      ∀ (x : (Fin n → R) × (Fin n → R)), τ.getLast? = some x →
        x ∉ {y : (Fin n → R) × (Fin n → R) | ∀ z ∈ [(u, w)], z.2 ⬝ᵥ y.1 = 0} → τ.length ≤ p →
        ExactAt (linkIn {x | x ∈ splitSeq R n ∧ ∀ y ∈ x, ∀ z ∈ [(u, w)], y.2 ⬝ᵥ z.1 = 0}
          {y : (Fin n → R) × (Fin n → R) | ∀ z ∈ [(u, w)], z.2 ⬝ᵥ y.1 = 0} τ) (p - τ.length) := by
    intro τ hτ x hlast hxS hlen
    obtain ⟨ρ, hρ, hρlen, hlink⟩ := GlobalTheory.T.exists_splitSeq_linkIn_orthogonal_eq_linkIn R n _ τ hγF hτ.1 hτ.2
    rw [hlink]
    have ht : 1 ≤ τ.length := by
      cases τ with
      | nil => simp at hlast
      | cons a t => simp
    simp only [List.length_singleton] at hρlen
    refine GlobalTheory.T.exactAt_linkIn_splitSeq_of_exactAt_splitSeq R s hs n (n - ρ.length) (p - τ.length) ρ hρ ?_ ?_ ?_
    · omega
    · omega
    · apply hlow
      · omega
      · omega
  obtain ⟨b1, hb1, hc1, hz1⟩ := GlobalTheory.T.exists_homologous_cycle_with_entries_in_of_exactAt_links _ _ _ hG'sc p hlinks c hc hcz
  have hcone : ∀ l ∈ linkIn {x | x ∈ splitSeq R n ∧ ∀ y ∈ x, ∀ z ∈ [(u, w)], y.2 ⬝ᵥ z.1 = 0}
      {y : (Fin n → R) × (Fin n → R) | ∀ z ∈ [(u, w)], z.2 ⬝ᵥ y.1 = 0} [],
      (u, w) :: l ∈ splitSeq R n := by
    intro l hl
    obtain ⟨hlS, hlG⟩ := hl
    simp only [List.nil_append] at hlG
    obtain ⟨hlF, hlo⟩ := hlG
    rw [hchar] at hlF ⊢
    refine ⟨?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hwu
      · exact hlF.1 y hy
    · rw [List.pairwise_cons]
      refine ⟨fun z hz => ⟨?_, ?_⟩, hlF.2⟩
      · simpa using hlS z hz
      · simpa using hlo z hz
  obtain ⟨b2, hb2, hbd2⟩ := GlobalTheory.T.seqChain_cycle_bounded_by_cone _ (splitSeq R n) _ (u, w) hcone p _ hc1 hz1
  refine ⟨b1 + b2, ?_, ?_⟩
  · refine Submodule.add_mem _ ?_ hb2
    refine Finsupp.supported_mono ?_ hb1
    intro l hl
    exact ⟨hl.1.1, hl.2⟩
  · rw [map_add, hbd2]
    abel

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL
theorem _root_.GlobalTheory.T.exists_bd_of_cycle_forms_kill_unimodular_vector : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ n : ℕ, (∀ n' < n, ∀ p' : ℕ, 2 * p' + s + 1 ≤ n' → ExactAt (splitSeq R n') p') → ∀ (p : ℕ) (u : Fin n → R), [u] ∈ uniSeq R n → 2 * p + s + 1 ≤ n → ∀ c ∈ chains {σ | σ ∈ splitSeq R n ∧ ∀ y ∈ σ, ∀ v ∈ [u], y.2 ⬝ᵥ v = 0} p, bd _ c = 0 → ∃ b ∈ chains (splitSeq R n) (p + 1), bd _ b = c := by
  first
  | exact @GlobalTheory.SeqCx.cycle_formsKill_bound_splitSeq
end
