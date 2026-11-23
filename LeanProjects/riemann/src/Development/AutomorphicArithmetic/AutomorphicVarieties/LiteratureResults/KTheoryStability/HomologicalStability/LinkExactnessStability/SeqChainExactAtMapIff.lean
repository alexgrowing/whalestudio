import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SubClosed

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCxMap

theorem bd_mapDomain {V W : Type} (e : V → W) (c : List V →₀ ℤ) :
    bd W (Finsupp.lmapDomain ℤ ℤ (List.map e) c) = Finsupp.lmapDomain ℤ ℤ (List.map e) (bd V c) := by
  have key : (bd W).comp (Finsupp.lmapDomain ℤ ℤ (List.map e)) =
      (Finsupp.lmapDomain ℤ ℤ (List.map e)).comp (bd V) := by
    apply Finsupp.lhom_ext
    intro l n
    simp [bd, Finsupp.linearCombination_single, Finsupp.mapDomain_single, Finset.smul_sum,
      Finsupp.mapDomain_finset_sum, Finsupp.mapDomain_smul, List.eraseIdx_map,
      ← Finsupp.single_mul]
  exact LinearMap.congr_fun key c

theorem chains_map {V W : Type} (e : V → W) (F : Set (List V)) (q : ℕ) :
    chains (List.map e '' F) q = (chains F q).map (Finsupp.lmapDomain ℤ ℤ (List.map e)) := by
  unfold chains
  rw [Finsupp.lmapDomain_supported]
  congr 1
  ext l
  constructor
  · rintro ⟨⟨l', hl', rfl⟩, hlen⟩
    exact ⟨l', ⟨hl', by simpa using hlen⟩, rfl⟩
  · rintro ⟨l', ⟨hl', hlen⟩, rfl⟩
    exact ⟨⟨l', hl', rfl⟩, by simpa using hlen⟩

end GlobalTheory.SeqCxMap

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.seqChain_exactAt_map_iff : ∀ (V W : Type) (e : V → W), Function.Injective e → ∀ (F : Set (List V)) (p : ℕ), ExactAt (List.map e '' F) p ↔ ExactAt F p := by
  intro V W e he F p
  have hinj : Function.Injective (Finsupp.lmapDomain ℤ ℤ (List.map e)) := by
    intro x y hxy
    exact Finsupp.mapDomain_injective (List.map_injective_iff.mpr he) hxy
  unfold GlobalTheory.SeqCx.ExactAt
  constructor
  · intro h c hc hbc
    obtain ⟨b, hb, hbb⟩ := h (Finsupp.lmapDomain ℤ ℤ (List.map e) c)
      (by rw [GlobalTheory.SeqCxMap.chains_map]; exact Submodule.mem_map_of_mem hc)
      (by rw [GlobalTheory.SeqCxMap.bd_mapDomain, hbc, map_zero])
    rw [GlobalTheory.SeqCxMap.chains_map] at hb
    obtain ⟨b', hb', rfl⟩ := hb
    exact ⟨b', hb', hinj (by rw [← GlobalTheory.SeqCxMap.bd_mapDomain]; exact hbb)⟩
  · intro h c hc hbc
    rw [GlobalTheory.SeqCxMap.chains_map] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    obtain ⟨b', hb', hbb⟩ := h c' hc'
      (hinj (by rw [← GlobalTheory.SeqCxMap.bd_mapDomain, hbc, map_zero]))
    refine ⟨Finsupp.lmapDomain ℤ ℤ (List.map e) b', ?_, ?_⟩
    · rw [GlobalTheory.SeqCxMap.chains_map]; exact Submodule.mem_map_of_mem hb'
    · rw [GlobalTheory.SeqCxMap.bd_mapDomain, hbb]
end
