import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff

noncomputable section

namespace GlobalTheory.SeqCx

open Finsupp

theorem map_supported_mem {α β : Type} {S : Set α}
    (f : (α →₀ ℤ) →ₗ[ℤ] (β →₀ ℤ)) (P : Submodule ℤ (β →₀ ℤ)) (h : ∀ z ∈ S, f (Finsupp.single z 1) ∈ P) :
    ∀ x ∈ Finsupp.supported ℤ ℤ S, f x ∈ P := by
  intro x hx
  rw [← Finsupp.sum_single x, Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun a ha => ?_
  rw [← Finsupp.smul_single_one, map_zsmul]
  exact P.smul_mem _ (h a (hx ha))

theorem hbd_single (V W : Type) (z : List V × List W) :
    hbd V W (Finsupp.single z 1) =
      ∑ i ∈ Finset.range z.1.length, (-1 : ℤ) ^ i • Finsupp.single (z.1.eraseIdx i, z.2) (1 : ℤ) := by
  simp only [hbd, bd, Finsupp.linearCombination_single, one_smul, Finsupp.mapDomain_finset_sum,
    Finsupp.mapDomain_smul, Finsupp.mapDomain_single]

theorem vbd_single (V W : Type) (z : List V × List W) :
    vbd V W (Finsupp.single z 1) =
      ∑ i ∈ Finset.range z.2.length, (-1 : ℤ) ^ i • Finsupp.single (z.1, z.2.eraseIdx i) (1 : ℤ) := by
  simp only [vbd, bd, Finsupp.linearCombination_single, one_smul, Finsupp.mapDomain_finset_sum,
    Finsupp.mapDomain_smul, Finsupp.mapDomain_single]

theorem bd_chains2 : ∀ (V W : Type) (D : Set (List V × List W)), SubClosed2 D →
    (∀ a b, ∀ x ∈ chains2 D (a + 1) b, hbd V W x ∈ chains2 D a b) ∧
    (∀ a b, ∀ x ∈ chains2 D a (b + 1), vbd V W x ∈ chains2 D a b) ∧
    (∀ b, ∀ x ∈ chains2 D 0 b, hbd V W x = 0) := by
  intro V W D hD
  refine ⟨fun a b => ?_, fun a b => ?_, fun b => ?_⟩
  · refine map_supported_mem (hbd V W) _ ?_
    rintro z ⟨hz, h1, h2⟩
    rw [hbd_single]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
    refine Finsupp.single_mem_supported ℤ _ ?_
    have hi' : i < z.1.length := Finset.mem_range.mp hi
    refine ⟨hD z hz _ _ (List.eraseIdx_sublist _ _) (List.Sublist.refl _), ?_, h2⟩
    rw [List.length_eraseIdx_of_lt hi', h1]
    rfl
  · refine map_supported_mem (vbd V W) _ ?_
    rintro z ⟨hz, h1, h2⟩
    rw [vbd_single]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
    refine Finsupp.single_mem_supported ℤ _ ?_
    have hi' : i < z.2.length := Finset.mem_range.mp hi
    refine ⟨hD z hz _ _ (List.Sublist.refl _) (List.eraseIdx_sublist _ _), h1, ?_⟩
    rw [List.length_eraseIdx_of_lt hi', h2]
    rfl
  · intro x hx
    have := map_supported_mem (hbd V W) (⊥ : Submodule ℤ _) ?_ x hx
    · simpa using this
    rintro z ⟨_, h1, _⟩
    rw [hbd_single, h1]
    simp

end GlobalTheory.SeqCx

end

section
open GlobalTheory.SeqCx
theorem _root_.GlobalTheory.T.pairSeqBoundaries_lower_bidegree_of_subClosed : ∀ (V W : Type) (D : Set (List V × List W)), SubClosed2 D → (∀ a b, ∀ x ∈ chains2 D (a + 1) b, hbd V W x ∈ chains2 D a b) ∧ (∀ a b, ∀ x ∈ chains2 D a (b + 1), vbd V W x ∈ chains2 D a b) ∧ (∀ b, ∀ x ∈ chains2 D 0 b, hbd V W x = 0) := by
  first
  | exact @GlobalTheory.SeqCx.bd_chains2
  | exact @GlobalTheory.SeqCx.vbd_single
  | exact @GlobalTheory.SeqCx.hbd_single
  | exact @GlobalTheory.SeqCx.map_supported_mem
end
