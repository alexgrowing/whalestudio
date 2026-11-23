import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExactAtUnimodularSeqsOfLinkNilCoordSubspace
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.LinksUnimodularSeqExactInStableRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SeqChainCycleBoundedByCone

open GlobalTheory.SeqCx Matrix UpperTheory.V.KL

namespace GlobalTheory

theorem subsingleton_of_stableRangeLe_zero (R : Type) [CommRing R] (h : StableRangeLe R 0) :
    Subsingleton R := by
  have hu : Unimodular R (fun _ : Fin 1 => (1 : R)) :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩) isUnit_one
  obtain ⟨t, ht⟩ := h 0 le_rfl (fun _ => 1) hu
  have h1 : (1 : R) ∈ Ideal.span (Set.range fun i : Fin 0 => (1 : R) + t i * 1) := by
    rw [show Ideal.span (Set.range fun i : Fin 0 => (1 : R) + t i * 1) = ⊤ from ht]
    exact Submodule.mem_top
  rw [Set.range_eq_empty, Ideal.span_empty, Ideal.mem_bot] at h1
  exact subsingleton_of_zero_eq_one h1.symm

theorem uniSeq_exactAt_of_stableRangeLe : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s →
    ∀ m q : ℕ, q + s ≤ m → ExactAt (uniSeq R m) q := by
  intro R _ s h m q hq
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · haveI := subsingleton_of_stableRangeLe_zero R h
    have hall : ∀ l : List (Fin m → R), l ∈ uniSeq R m :=
      fun l => ⟨fun _ => 0, fun _ _ => Subsingleton.elim _ _⟩
    exact GlobalTheory.T.seqChain_cycle_bounded_by_cone (Fin m → R) (uniSeq R m) (uniSeq R m) 0 (fun l _ => hall _) q
  · have hL := (GlobalTheory.SeqCx.linkExact_of_stableRangeLe R s h hs m).1
    exact GlobalTheory.T.exactAt_unimodularSeqs_of_link_nil_coordSubspace R m q (hL [] ⟨fun _ => 0, fun i _ => i.elim0⟩ q (by simpa using hq))

end GlobalTheory

section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL
theorem _root_.GlobalTheory.T.exactAt_unimodularSeqs_of_add_stableRank_le : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ m q : ℕ, q + s ≤ m → ExactAt (uniSeq R m) q := by
  first
  | exact @GlobalTheory.uniSeq_exactAt_of_stableRangeLe
  | exact @GlobalTheory.subsingleton_of_stableRangeLe_zero
end
