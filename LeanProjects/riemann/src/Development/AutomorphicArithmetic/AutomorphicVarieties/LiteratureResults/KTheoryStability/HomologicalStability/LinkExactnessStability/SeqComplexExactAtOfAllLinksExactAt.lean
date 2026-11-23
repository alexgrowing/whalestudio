import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SubClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsHomologousCycleWithEntriesInOfExactAtLinks

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory

theorem SeqCx.exactAt_of_links : ∀ (V : Type) (F : Set (List V)) (S : Set V), SubClosed F → ∀ (p : ℕ),
    (∀ τ ∈ F, τ.length ≤ p → ExactAt (linkIn F S τ) (p - τ.length)) → ExactAt F p := by
  intro V F S hF p h c hc hcb
  have hsubF : ∀ q, chains (linkIn F S []) q ≤ chains F q := by
    intro q
    apply Finsupp.supported_mono
    rintro l ⟨⟨_, hl⟩, hlen⟩
    exact ⟨by simpa using hl, hlen⟩
  by_cases h0 : ([] : List V) ∈ F
  · obtain ⟨b, hb, hcb', hcyc⟩ :=
      T.exists_homologous_cycle_with_entries_in_of_exactAt_links V F S hF p (fun τ hτ _ _ _ hl => h τ hτ hl) c hc hcb
    obtain ⟨b', hb', hbd⟩ := h [] h0 (by simp) (c - bd V b) (by simpa using hcb') hcyc
    refine ⟨b + b', (chains F (p + 1)).add_mem hb (hsubF _ (by simpa using hb')), ?_⟩
    rw [map_add, hbd]
    abel
  · have hFe : ∀ l, l ∉ F := fun l hl => h0 (hF l hl [] (List.nil_sublist l))
    have hc0 : c = 0 := by
      have : {l : List V | l ∈ F ∧ l.length = p} = ∅ := by
        ext l
        simp [hFe l]
      have hc' := hc
      simp only [chains, this, Finsupp.supported_empty, Submodule.mem_bot] at hc'
      exact hc'
    exact ⟨0, Submodule.zero_mem _, by simp [hc0]⟩

end GlobalTheory

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.seqComplex_exactAt_of_all_links_exactAt : ∀ (V : Type) (F : Set (List V)) (S : Set V), SubClosed F → ∀ (p : ℕ), (∀ τ ∈ F, τ.length ≤ p → ExactAt (linkIn F S τ) (p - τ.length)) → ExactAt F p := by
  first
  | exact @GlobalTheory.SeqCx.exactAt_of_links
end
