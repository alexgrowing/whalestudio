import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHermitianOrbitSumFixedLengthLtTop
open Filter Topology

namespace GlobalTheory.InvolutionNorm

theorem exists_compact_mod_kernel : ∀ (Z : Type) [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [LocallyCompactSpace Z] [SigmaCompactSpace Z] [T2Space Z], (∀ a b : Z, a * b = b * a) → ∀ τ : Z →* Z, Continuous τ → (∀ z, τ (τ z) = z) → (∃ W ∈ nhds (1 : Z), ∀ s ∈ W, τ s = s → ∃ r : Z, τ r = r ∧ r * r = s) → ∀ D : Set Z, IsCompact D → ∃ B : Set Z, IsCompact B ∧ ∀ z : Z, τ z * z ∈ D → ∃ t : Z, τ t * t = 1 ∧ ∃ b ∈ B, z = t * b := by
  intro Z _ _ _ _ _ _ hc τ hτ hinv hW D hD
  obtain ⟨W, hW1, hWs⟩ := hW
  let N : Z →* Z :=
    { toFun := fun z => τ z * z
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul]
        rw [mul_assoc, mul_assoc, ← mul_assoc (τ b) a b, hc (τ b) a, mul_assoc] }
  have hN : Continuous N := hτ.mul continuous_id
  have hNval : ∀ z, N z = τ z * z := fun _ => rfl
  let I : Subgroup Z := N.range
  have hIH : ∀ y ∈ I, τ y = y := by
    rintro _ ⟨z, rfl⟩
    rw [hNval, map_mul, hinv, hc]
  have hHcl : IsClosed {y : Z | τ y = y} := isClosed_eq hτ continuous_id
  have hIcl : IsClosed (I : Set Z) := by
    refine closure_subset_iff_isClosed.1 fun x hx => ?_
    have hxH : τ x = x := closure_minimal (fun y hy => hIH y hy) hHcl hx
    have hnb : (fun y => x⁻¹ * y) ⁻¹' W ∈ 𝓝 x := by
      refine (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds ?_
      simpa using hW1
    obtain ⟨i, hiW, hiI⟩ := mem_closure_iff_nhds.1 hx _ hnb
    have hiH : τ i = i := hIH i hiI
    obtain ⟨r, hr, hrr⟩ := hWs _ hiW (by rw [map_mul, map_inv, hxH, hiH])
    have hNr : N r = x⁻¹ * i := by rw [hNval, hr, hrr]
    have : x = i * (N r)⁻¹ := by rw [hNr]; group
    rw [this]
    exact I.mul_mem hiI (I.inv_mem ⟨r, rfl⟩)
  let f : Z →* I := N.rangeRestrict
  have hfc : Continuous f := hN.subtype_mk _
  have hfs : Function.Surjective f := N.rangeRestrict_surjective
  have : LocallyCompactSpace I := hIcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hopen : IsOpenMap f := f.isOpenMap_of_sigmaCompact hfs hfc
  have hK' : IsCompact (Subtype.val ⁻¹' D : Set I) :=
    hIcl.isClosedEmbedding_subtypeVal.isCompact_preimage hD
  have key : ∃ C : Set Z, IsCompact C ∧ (Subtype.val ⁻¹' D : Set I) ⊆ f '' C := by
    refine hK'.induction_on (p := fun s => ∃ C : Set Z, IsCompact C ∧ s ⊆ f '' C)
      ⟨∅, isCompact_empty, Set.empty_subset _⟩ (fun s t hst ⟨C, hC, h⟩ => ⟨C, hC, hst.trans h⟩) ?_ ?_
    · rintro s t ⟨C, hC, h⟩ ⟨D, hD, h'⟩
      exact ⟨C ∪ D, hC.union hD, by rw [Set.image_union]; exact Set.union_subset_union h h'⟩
    · intro y _
      obtain ⟨g, rfl⟩ := hfs y
      obtain ⟨C, hC, hg⟩ := exists_compact_mem_nhds g
      exact ⟨_, mem_nhdsWithin_of_mem_nhds (hopen.image_mem_nhds hg), C, hC, subset_rfl⟩
  obtain ⟨C, hC, hCD⟩ := key
  refine ⟨C, hC, fun z hz => ?_⟩
  obtain ⟨c, hcC, e⟩ := hCD (a := f z) hz
  have e' : N c = N z := congrArg Subtype.val e
  refine ⟨z * c⁻¹, ?_, c, hcC, by group⟩
  rw [← hNval, map_mul, map_inv, e', mul_inv_cancel]

end GlobalTheory.InvolutionNorm
