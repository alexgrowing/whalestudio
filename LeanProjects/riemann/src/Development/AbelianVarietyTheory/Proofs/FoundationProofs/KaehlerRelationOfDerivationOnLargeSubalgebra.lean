import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne

noncomputable section

namespace GlobalTheory.AlmostEt

open Finsupp

theorem kerTotal_gen_local {A S : Type} [CommRing A] [CommRing S] [Algebra A S]
    (g : S →₀ S)
    (hg : g ∈ ((Set.range fun x : S × S => single x.1 1 + single x.2 1 - single (x.1 + x.2) 1) ∪
        Set.range fun x : S × S => single x.2 x.1 + single x.1 x.2 - single (x.1 * x.2) 1) ∪
      Set.range fun x : A => single (algebraMap A S x) 1) :
    ∃ F : Finset S, ∀ C : Subalgebra A S, (↑F : Set S) ⊆ C →
      ∀ (M : Type) [AddCommGroup M] [Module S M] (D : S → M), IsDerOn C D →
        Finsupp.linearCombination S D g = 0 := by
  classical
  rcases hg with (⟨⟨u, w⟩, rfl⟩ | ⟨⟨u, w⟩, rfl⟩) | ⟨a, rfl⟩
  · refine ⟨{u, w}, fun C hC M _ _ D hD => ?_⟩
    have hu : u ∈ C := hC (by simp)
    have hw : w ∈ C := hC (by simp)
    simp [hD.add u hu w hw]
  · refine ⟨{u, w}, fun C hC M _ _ D hD => ?_⟩
    have hu : u ∈ C := hC (by simp)
    have hw : w ∈ C := hC (by simp)
    simp [hD.mul u hu w hw, add_comm]
  · refine ⟨∅, fun C _ M _ _ D hD => ?_⟩
    simp [hD.alg a]

theorem kaehler_rel_local : ∀ (A S : Type) [CommRing A] [CommRing S] [Algebra A S] (n : ℕ)
    (x y : Fin n → S), ∑ i, x i • KaehlerDifferential.D A S (y i) = 0 →
    ∃ T : Finset S, ∀ C : Subalgebra A S, (↑T : Set S) ⊆ C → (∀ i, y i ∈ C) →
      ∀ (M : Type) [AddCommGroup M] [Module S M] (D : S → M), IsDerOn C D →
        ∑ i, x i • D (y i) = 0 := by
  intro A S _ _ _ n x y h
  classical
  set v : S →₀ S := ∑ i, single (y i) (x i) with hv
  have hlc : ∀ (M : Type) [AddCommGroup M] [Module S M] (D : S → M),
      Finsupp.linearCombination S D v = ∑ i, x i • D (y i) := by
    intro M _ _ D
    simp [hv, map_sum, Finsupp.linearCombination_single]
  have hmem : v ∈ KaehlerDifferential.kerTotal A S := by
    rw [← KaehlerDifferential.kerTotal_eq, LinearMap.mem_ker, hlc, h]
  obtain ⟨G, hGs, hvG⟩ := Submodule.mem_span_finite_of_mem_span hmem
  have key := fun g (hg : g ∈ G) => kerTotal_gen_local (A := A) g (hGs hg)
  choose F hF using key
  refine ⟨G.attach.biUnion (fun g => F g.1 g.2), ?_⟩
  intro C hC _ M _ _ D hD
  rw [← hlc]
  have hle : Submodule.span S (↑G : Set (S →₀ S)) ≤
      LinearMap.ker (Finsupp.linearCombination S D) := by
    rw [Submodule.span_le]
    intro g hg
    refine hF g hg C (fun z hz => hC ?_) M D hD
    simp only [Finset.coe_biUnion, Finset.coe_attach, Set.mem_univ, Set.iUnion_true,
      Set.mem_iUnion]
    exact ⟨⟨g, hg⟩, hz⟩
  exact hle hvG

end GlobalTheory.AlmostEt
