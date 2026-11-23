import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PhiMapAdd

noncomputable section

open scoped Classical Pointwise
open MeasureTheory NumberField NumberField.mixedEmbedding

namespace Formalism.L2.SG.NGCut.SplitEmbedding

theorem idealCovol (K : Type) [Field K] [NumberField K] [IsEmpty {w : InfinitePlace K // w.IsReal}]
    (ι : Type) [Fintype ι] (φ : ι → (K →+* ℂ)) (σ : ι ≃ {w : InfinitePlace K // w.IsComplex})
    (hφ : ∀ i, φ i = (σ i).1.embedding ∨ φ i = ComplexEmbedding.conjugate (σ i).1.embedding)
    (I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) (Λ : AddSubgroup K)
    (hΛ : ∀ a ∈ Λ, a ∈ (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) (k : ℕ)
    (hk : Λ.relIndex (((I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K).toAddSubgroup) = k)
    (hk0 : k ≠ 0) (s : ℝ) (hs : s ≠ 0) (F : Set (ι → ℂ)) (hF : MeasurableSet F)
    (hFd : ∀ v, ∃! a : Λ, (fun i => (s : ℂ) * φ i a) + v ∈ F) :
    volume F = ENNReal.ofReal ((k : ℝ) * (FractionalIdeal.absNorm (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) *
      2⁻¹ ^ Fintype.card ι * √|(discr K : ℝ)| * |s| ^ (2 * Fintype.card ι)) := by
  set cj : ι → Prop := fun i => φ i ≠ (σ i).1.embedding
  have hψ : MeasurePreserving (phiMap σ cj (K := K)) volume volume := phiMap_mp σ cj
  have hψe : ∀ a : K, phiMap σ cj (mixedEmbedding K a) = fun i => φ i a := by
    intro a; funext i
    simp only [phiMap, mixedEmbedding_apply_isComplex]
    by_cases hi : cj i
    · rw [if_pos hi]
      rcases hφ i with h | h
      · exact absurd h hi
      · rw [h, ComplexEmbedding.conjugate_coe_eq]
    · rw [if_neg hi]
      have : φ i = (σ i).1.embedding := not_not.1 hi
      rw [this]
  set emb : K →+ mixedSpace K := (mixedEmbedding K).toAddMonoidHom
  have hinj : Function.Injective emb := mixedEmbedding_injective K
  set Λm := Λ.map emb
  set G := phiMap σ cj (K := K) ⁻¹' (s⁻¹ • F)
  have hGm : MeasurableSet G := hψ.measurable (hF.const_smul₀ (s⁻¹))
  have hmem : ∀ y : ι → ℂ, y ∈ s⁻¹ • F ↔ s • y ∈ F := by
    intro y
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hs), inv_inv]
  have hsm : ∀ a : K, ∀ x : mixedSpace K, s • phiMap σ cj (emb a + x) = (fun i => (s : ℂ) * φ i a) + s • phiMap σ cj x := by
    intro a x
    rw [phiMap_add, smul_add, show emb a = mixedEmbedding K a from rfl, hψe]
    funext i
    simp [Complex.real_smul]
  have hdG : ∀ x, ∃! b : Λm, (b : mixedSpace K) + x ∈ G := by
    intro x
    obtain ⟨a, ha, hu⟩ := hFd (s • phiMap σ cj x)
    refine ⟨⟨emb a, AddSubgroup.mem_map_of_mem emb a.2⟩, ?_, ?_⟩
    · show phiMap σ cj (emb a + x) ∈ s⁻¹ • F
      rw [hmem, hsm]; exact ha
    · rintro ⟨b, hb⟩ hbG
      obtain ⟨a', ha', rfl⟩ := AddSubgroup.mem_map.1 hb
      have h1 : (fun i => (s : ℂ) * φ i (⟨a', ha'⟩ : Λ)) + s • phiMap σ cj x ∈ F := by
        have : phiMap σ cj (emb a' + x) ∈ s⁻¹ • F := hbG
        rw [hmem, hsm] at this; exact this
      have := hu ⟨a', ha'⟩ h1
      apply Subtype.ext
      show emb a' = emb a
      rw [show a' = (a : K) from congrArg Subtype.val this]

  set L := (idealLattice K I).toAddSubgroup
  have hL : L = (((I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K).toAddSubgroup).map emb := by
    ext x
    simp only [L, Submodule.mem_toAddSubgroup, mem_idealLattice, AddSubgroup.mem_map]
    rfl
  have hle : Λm ≤ L := by
    rw [hL]; exact AddSubgroup.map_mono (fun a ha => hΛ a ha)
  have hk' : Λm.relIndex L = k := by
    rw [hL, AddSubgroup.relIndex_map_map_of_injective _ _ hinj, hk]
  have hcount : Countable L := by
    have b := Module.Free.chooseBasis ℤ (idealLattice K I)
    exact (Module.Free.chooseBasis ℤ (idealLattice K I)).equivFun.injective.countable
  set b := Module.Free.chooseBasis ℤ (idealLattice K I)
  set b' := Module.Basis.ofZLatticeBasis ℝ (idealLattice K I) b
  set FL := ZSpan.fundamentalDomain b'
  have hFLm : MeasurableSet FL := ZSpan.fundamentalDomain_measurableSet b'
  have hspan := Module.Basis.ofZLatticeBasis_span ℝ (idealLattice K I) b
  have hdL : ∀ x, ∃! l : L, (l : mixedSpace K) + x ∈ FL := by
    intro x
    obtain ⟨v, hv, hu⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b' x
    have hvL : (v : mixedSpace K) ∈ idealLattice K I :=
      (congrArg (fun S : Submodule ℤ (mixedSpace K) => (v : mixedSpace K) ∈ S) hspan).mp v.2
    refine ⟨⟨v, hvL⟩, hv, ?_⟩
    rintro ⟨l, hl⟩ hlF
    have hl' : l ∈ Submodule.span ℤ (Set.range b') :=
      (congrArg (fun S : Submodule ℤ (mixedSpace K) => l ∈ S) hspan).mpr hl
    have h3 := hu ⟨l, hl'⟩ hlF
    have h2 : l = (v : mixedSpace K) := by rw [← h3]
    exact Subtype.ext h2
  have hidx := fund_index (volume : Measure (mixedSpace K)) L Λm hle k hk' hk0 FL G hFLm hGm hdL hdG

  have hfd := ZLattice.isAddFundamentalDomain b (volume : Measure (mixedSpace K))
  have hcov := ZLattice.covolume_eq_measure_fundamentalDomain (idealLattice K I) volume hfd
  rw [covolume_idealLattice] at hcov
  have hfin : volume FL ≠ ⊤ := (ZSpan.fundamentalDomain_isBounded b').measure_lt_top.ne
  have hFLv : volume FL = ENNReal.ofReal ((FractionalIdeal.absNorm (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) *
      2⁻¹ ^ InfinitePlace.nrComplexPlaces K * √|(discr K : ℝ)|) := by
    rw [hcov, measureReal_def, ENNReal.ofReal_toReal hfin]
  have hr2 : InfinitePlace.nrComplexPlaces K = Fintype.card ι := by
    rw [InfinitePlace.nrComplexPlaces, Fintype.card_congr σ.symm]

  have hGv : volume G = volume (s⁻¹ • F) := hψ.measure_preimage (hF.const_smul₀ (s⁻¹)).nullMeasurableSet
  have hscale : volume F = ENNReal.ofReal |s ^ Module.finrank ℝ (ι → ℂ)| * volume (s⁻¹ • F) := by
    conv_lhs => rw [← smul_inv_smul₀ hs F]
    exact Measure.addHaar_smul volume s (s⁻¹ • F)
  have hdim : Module.finrank ℝ (ι → ℂ) = 2 * Fintype.card ι := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  rw [hscale, ← hGv, hidx, hFLv, hr2, hdim]
  rw [← ENNReal.ofReal_natCast k, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  rw [abs_pow]
  ring

end Formalism.L2.SG.NGCut.SplitEmbedding
