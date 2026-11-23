import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.PosSemidefOfForallCombination
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.InhabSt
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder

namespace GlobalTheory.AdaptedFrameIndex

theorem relIndex_span_append_le : ∀ (K : Type) [Field K] [NumberField K] (m m' : ℕ)
    (q : (Fin m → K) →ₗ[K] (Fin m' → K)) (W : Submodule (𝓞 K) (Fin m → K)), W.FG →
    ∀ (s t : ℕ) (a : Fin s → Fin m → K) (b : Fin t → Fin m → K),
    IsFrame K (W ⊓ (LinearMap.ker q).restrictScalars (𝓞 K)) a → IsFrame K W (Fin.append a b) →
    (Submodule.span (𝓞 K) (Set.range (Fin.append a b))).toAddSubgroup.relIndex W.toAddSubgroup ≤
      (Submodule.span (𝓞 K) (Set.range a)).toAddSubgroup.relIndex
        (W ⊓ (LinearMap.ker q).restrictScalars (𝓞 K)).toAddSubgroup *
      (Submodule.span (𝓞 K) (Set.range (q ∘ b))).toAddSubgroup.relIndex
        (W.map (q.restrictScalars (𝓞 K))).toAddSubgroup := by
  intro K _ _ m m' q W hW s t a b ha hu
  set qR := q.restrictScalars (𝓞 K) with hqR
  set kR := (LinearMap.ker q).restrictScalars (𝓞 K) with hkR
  set f : (Fin m → K) →+ (Fin m' → K) := qR.toAddMonoidHom with hf
  set Hs := Submodule.span (𝓞 K) (Set.range (Fin.append a b)) with hHs
  set H := Hs.toAddSubgroup with hH
  set G := W.toAddSubgroup with hG
  set Gk := (W ⊓ kR).toAddSubgroup with hGk
  set Sa := (Submodule.span (𝓞 K) (Set.range a)).toAddSubgroup with hSa
  set Sb := (Submodule.span (𝓞 K) (Set.range (q ∘ b))).toAddSubgroup with hSb
  have hHG : H ≤ G := Submodule.toAddSubgroup_mono
    (Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hu.1 i))
  have hGkG : Gk ≤ G := Submodule.toAddSubgroup_mono inf_le_left
  have hM : H ⊔ Gk ≤ G := sup_le hHG hGkG
  have hmul := AddSubgroup.relIndex_mul_relIndex H (H ⊔ Gk) G le_sup_left hM
  have h1 : H.relIndex (H ⊔ Gk) = H.relIndex Gk := by
    rw [sup_comm]; exact AddSubgroup.relIndex_sup_right Gk H
  have hFG : (W ⊓ kR).FG := by
    haveI := isNoetherian_of_fg_of_noetherian W hW
    exact Submodule.FG.of_le_of_isNoetherian inf_le_left
  have hSa0 : Sa.relIndex Gk ≠ 0 := IsFrame.relIndex_ne_zero hFG ha
  have hSaH : Sa ≤ H := Submodule.toAddSubgroup_mono (Submodule.span_mono (by
    rintro _ ⟨i, rfl⟩; exact ⟨Fin.castAdd t i, Fin.append_left _ _ _⟩))
  have h2 : H.relIndex Gk ≤ Sa.relIndex Gk := AddSubgroup.relIndex_le_of_le_left hSaH hSa0
  have h3 : H ⊔ Gk = (H.map f).comap f ⊓ G := by
    ext x
    constructor
    · intro hx
      refine ⟨?_, hM hx⟩
      obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.mp hx
      have hz0 : q z = 0 := hz.2
      refine AddSubgroup.mem_map.mpr ⟨y, hy, ?_⟩
      show q y = q (y + z)
      rw [map_add, hz0, add_zero]
    · rintro ⟨hx1, hx2⟩
      obtain ⟨y, hy, hyx⟩ := AddSubgroup.mem_map.mp (AddSubgroup.mem_comap.mp hx1)
      have hyx' : q y = q x := hyx
      refine AddSubgroup.mem_sup.mpr ⟨y, hy, x - y, ⟨?_, ?_⟩, by abel⟩
      · exact W.sub_mem hx2 (hHG hy)
      · show q (x - y) = 0
        rw [map_sub, hyx', sub_self]
  have hM2 : (H ⊔ Gk).relIndex G = (H.map f).relIndex (G.map f) := by
    rw [h3, AddSubgroup.inf_relIndex_right, AddSubgroup.relIndex_comap]
  have hleS : Hs ≤ (Submodule.span (𝓞 K) (Set.range (q ∘ b))).comap qR := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]
      show q (a j) ∈ Submodule.span (𝓞 K) (Set.range (q ∘ b))
      rw [show q (a j) = 0 from (ha.1 j).2]
      exact Submodule.zero_mem _
    · rw [Fin.append_right]
      exact Submodule.subset_span ⟨j, rfl⟩
  have hSle : Submodule.span (𝓞 K) (Set.range (q ∘ b)) ≤ Hs.map qR := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    exact ⟨b j, Submodule.subset_span ⟨Fin.natAdd s j, Fin.append_right _ _ _⟩, rfl⟩
  have hmapH : H.map f = Sb := by
    apply le_antisymm
    · rw [AddSubgroup.map_le_iff_le_comap]
      intro x hx
      exact hleS hx
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp (hSle hy)
      exact AddSubgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hmapG : G.map f = (W.map qR).toAddSubgroup := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.mp hy
      exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
      exact AddSubgroup.mem_map.mpr ⟨x, hx, rfl⟩
  calc H.relIndex G = H.relIndex (H ⊔ Gk) * (H ⊔ Gk).relIndex G := hmul.symm
    _ = H.relIndex Gk * Sb.relIndex (W.map qR).toAddSubgroup := by rw [h1, hM2, hmapH, hmapG]
    _ ≤ Sa.relIndex Gk * Sb.relIndex (W.map qR).toAddSubgroup := Nat.mul_le_mul_right _ h2

end GlobalTheory.AdaptedFrameIndex
