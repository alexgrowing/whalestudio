import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocMulVec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthModuloSpanLeOfForallFinset
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.Pass.LocDirect

theorem lenMod_span_sUnion_le_of_directed : ∀ {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (S : Set (Set M)) (H : Submodule O M) (N : ℕ∞),
    (∀ A ∈ S, ∀ B ∈ S, ∃ C ∈ S, A ⊆ C ∧ B ⊆ C) →
    (∀ A ∈ S, BlochKatoDuality.lenMod (Submodule.span O A) H ≤ N) →
    BlochKatoDuality.lenMod (Submodule.span O (⋃₀ S)) H ≤ N := by
  intro O M _ _ _ S H N hdir hA
  classical
  apply GlobalTheory.Pass.LocDual.lenMod_span_le_of_finset
  intro F hF
  rcases S.eq_empty_or_nonempty with hS | ⟨A0, hA0⟩
  · have hF0 : (↑F : Set M) = ∅ := by
      rw [hS, Set.sUnion_empty] at hF
      exact Set.subset_empty_iff.mp hF
    rw [hF0, Submodule.span_empty, GlobalTheory.Pass.LocDual.lenMod_eq_height_map, Submodule.map_bot,
      Order.height_bot]
    exact zero_le
  · have key : ∀ G : Finset M, (↑G : Set M) ⊆ ⋃₀ S → ∃ A ∈ S, (↑G : Set M) ⊆ A := by
      intro G
      induction G using Finset.induction_on with
      | empty => intro _; exact ⟨A0, hA0, by simp⟩
      | insert a G ha ih =>
        intro hG
        rw [Finset.coe_insert, Set.insert_subset_iff] at hG
        obtain ⟨B, hB, haB⟩ := hG.1
        obtain ⟨A, hA', hGA⟩ := ih hG.2
        obtain ⟨C, hC, hAC, hBC⟩ := hdir A hA' B hB
        refine ⟨C, hC, ?_⟩
        rw [Finset.coe_insert, Set.insert_subset_iff]
        exact ⟨hBC haB, hGA.trans hAC⟩
    obtain ⟨A, hAS, hFA⟩ := key F hF
    refine le_trans ?_ (hA A hAS)
    rw [GlobalTheory.Pass.LocDual.lenMod_eq_height_map, GlobalTheory.Pass.LocDual.lenMod_eq_height_map]
    exact Order.height_mono (Submodule.map_mono (Submodule.span_mono hFA))

end GlobalTheory.Pass.LocDirect
