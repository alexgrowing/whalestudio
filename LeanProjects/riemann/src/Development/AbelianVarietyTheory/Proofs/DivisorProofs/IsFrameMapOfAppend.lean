import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.PosSemidefOfForallCombination
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.InhabSt
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder

namespace GlobalTheory

theorem isFrame_map_of_append_frame (K : Type) [Field K] [NumberField K] (m m' : ℕ)
    (q : (Fin m → K) →ₗ[K] (Fin m' → K)) (W : Submodule (𝓞 K) (Fin m → K)) (s t : ℕ)
    (a : Fin s → Fin m → K) (b : Fin t → Fin m → K)
    (ha : IsFrame K (W ⊓ (LinearMap.ker q).restrictScalars (𝓞 K)) a)
    (hab : IsFrame K W (Fin.append a b)) :
    IsFrame K (W.map (q.restrictScalars (𝓞 K))) (q ∘ b) := by
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hab1, hab2, hab3⟩ := hab
  have hbW : ∀ j, b j ∈ W := fun j => by simpa using hab1 (Fin.natAdd s j)
  have hqa : ∀ i, q (a i) = 0 := fun i => (ha1 i).2
  refine ⟨fun j => ⟨b j, hbW j, rfl⟩, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    set x : Fin m → K := ∑ j, g j • b j with hx
    have hqx : q x = 0 := by simpa [hx, map_sum, map_smul] using hg
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K)) Finset.univ g
    choose c hc using fun j => hd j (Finset.mem_univ j)
    have hd0 : ((d : 𝓞 K) : K) ≠ 0 := by
      have := nonZeroDivisors.coe_ne_zero d
      exact_mod_cast this
    have hdx : ((d : 𝓞 K) : K) • x = ∑ j, c j • b j := by
      rw [hx, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, ← algebraMap_smul K (c j) (b j), hc j, Algebra.smul_def]
      rfl
    have hdxW : ((d : 𝓞 K) : K) • x ∈ W ⊓ (LinearMap.ker q).restrictScalars (𝓞 K) := by
      refine ⟨?_, ?_⟩
      · rw [hdx]
        exact Submodule.sum_mem W fun j _ => W.smul_mem (c j) (hbW j)
      · simp [hqx]
    have hxa : x ∈ Submodule.span K (Set.range a) :=
      (Submodule.smul_mem_iff _ hd0).mp (ha3 hdxW)
    obtain ⟨h, hh⟩ := Submodule.mem_span_range_iff_exists_fun K |>.mp hxa
    rw [Fintype.linearIndependent_iff] at hab2
    have key := hab2 (Fin.append (fun i => -h i) g) (by
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, neg_smul, Finset.sum_neg_distrib, hh]
      simp [hx])
    intro j
    simpa using key (Fin.natAdd s j)
  · rintro y ⟨w, hw, rfl⟩
    have hle : Submodule.span K (Set.range (Fin.append a b)) ≤
        (Submodule.span K (Set.range (q ∘ b))).comap q := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      induction k using Fin.addCases with
      | left i => simp [hqa]
      | right j =>
        rw [SetLike.mem_coe, Submodule.mem_comap, Fin.append_right]
        exact Submodule.subset_span ⟨j, rfl⟩
    exact hle (hab3 hw)

end GlobalTheory
