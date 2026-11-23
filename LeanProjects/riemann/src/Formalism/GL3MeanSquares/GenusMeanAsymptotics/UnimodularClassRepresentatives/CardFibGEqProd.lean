import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SumOrbitsEquivariant
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AdjoinIntegralOfNonempty
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtIffVd
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomLocFOfVdZero

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem fibLoc_eq_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {Λ' : Submodule (𝓞 K) V'}
    (hΛ' : Submodule.IsLattice K Λ') (hΛi : Formalism.HermitianLatticesTheory.IsIntegralLat h' Λ') {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : h S.x₀ S.x₀ = algebraMap F K (n : F))
    (hvL : vd h L 𝔭 = 0) (hvn : vF 𝔭 n = 0) (hvΛ : vd h' Λ' 𝔭 = 0) : fibLoc S L 𝔭 Λ' = 1 := by
  classical
  rw [LocalizedFibreSets.fibLoc_eq_card]
  have hN : Submodule.IsLattice K (S.adjoin Λ') := (VecSplit.isLattice_adjoin_iff S Λ').2 hΛ'
  have hmk : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) n) = algebraMap F K (n : F) := rfl
  have hn1 : h S.x₀ S.x₀ ∈ (1 : Submodule (𝓞 K) K) := by
    rw [hn, ← hmk]
    exact Submodule.mem_one.2 ⟨_, rfl⟩
  have hNi : Formalism.HermitianLatticesTheory.IsIntegralLat h (S.adjoin Λ') := LocalizedFibreSets.isIntegralLat_adjoin hs S hn1 hΛi
  obtain ⟨P, hP, hPc⟩ := LocalizedFibreSets.exists_max_over (K := K) h𝔭
  have hne : algebraMap F K (n : F) ≠ 0 := by
    rw [← hn]
    exact S.hx₀
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hne (by simp)
  have hnP : n ∉ 𝔭 := LocalizedFibreSets.notMem_of_vF_zero h𝔭 hn0 hvn
  have hmP : algebraMap (𝓞 F) (𝓞 K) n ∉ P := by
    intro hm
    apply hnP
    rw [← hPc]
    exact hm
  have hvN : vd h (S.adjoin Λ') 𝔭 = 0 := by
    rw [← hPc, ← isUnimodularAt_iff_vd hK hF hs hd hN hNi hP]
    refine LocalizedFibreSets.unimod_adjoin hs S ?_ ?_ ?_
    · show ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P, s • h S.x₀ S.x₀ ∈ (1 : Submodule (𝓞 K) K)
      exact ⟨1, Submonoid.one_mem _, by simpa using hn1⟩
    · show ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P, s • (h S.x₀ S.x₀)⁻¹ ∈ (1 : Submodule (𝓞 K) K)
      refine ⟨algebraMap (𝓞 F) (𝓞 K) n, Submonoid.subset_closure ⟨hmP, ?_⟩, ?_⟩
      · intro t ht
        have hst : star (algebraMap F K (n : F)) = algebraMap F K (n : F) := (hF _).2 ⟨_, rfl⟩
        rw [hmk, hst, ← hmk] at ht
        rw [FaithfulSMul.algebraMap_injective (𝓞 K) K ht]
        exact hmP
      · rw [Algebra.smul_def, hmk, hn, mul_inv_cancel₀ hne]
        exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · rw [isUnimodularAt_iff_vd hK hF (S.isSymm hs) (S.isTotPosDef hd) hΛ' hΛi hP, hPc]
      exact hvΛ
  rw [LocalizedFibreSets.fibSet_eq_singleton hK hF hs hd S hL hLi hN hNi h𝔭 hvL hvN]
  simp

theorem card_fibG_eq_prod (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {Λ' : Submodule (𝓞 K) V'}
    (hΛ' : Submodule.IsLattice K Λ') :
    (Nat.card (fibG S L Λ') : ℝ) = ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (fibLoc S L 𝔭.1 Λ' : ℝ) := by
  classical
  by_cases hne : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (LocalizedFibreSets.fibSet S L 𝔭.1 Λ').Nonempty
  · have hN : Submodule.IsLattice K (S.adjoin Λ') := (VecSplit.isLattice_adjoin_iff S Λ').2 hΛ'
    have hNi := LocalizedFibreSets.adjoin_integral_of_nonempty hK hF S hLi hne
    obtain ⟨t, ht⟩ : ∃ t : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
        ∀ 𝔭 ∉ t, vd h L 𝔭.1 = 0 ∧ vd h (S.adjoin Λ') 𝔭.1 = 0 := by
      have hfin := (finite_vd_ne_zero hK hF hs hd hL hLi).union (finite_vd_ne_zero hK hF hs hd hN hNi)
      refine ⟨hfin.toFinset, fun 𝔭 h𝔭 => ?_⟩
      simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h𝔭
      exact h𝔭
    have ht1 : ∀ 𝔭 ∉ t, LocalizedFibreSets.fibSet S L 𝔭.1 Λ' = {locF 𝔭.1 (S.adjoin Λ')} := fun 𝔭 h𝔭 =>
      LocalizedFibreSets.fibSet_eq_singleton hK hF hs hd S hL hLi hN hNi 𝔭.2 (ht 𝔭 h𝔭).1 (ht 𝔭 h𝔭).2
    rw [LocalizedFibreSets.card_fibG_eq_card_pi hK hF S hL hΛ' t ht1, Nat.card_pi, Nat.cast_prod,
      tprod_eq_prod (s := t) (fun 𝔭 h𝔭 => by rw [LocalizedFibreSets.fibLoc_eq_card, ht1 𝔭 h𝔭]; simp)]
    rw [← Finset.prod_coe_sort t]
    exact Finset.prod_congr rfl fun 𝔭 _ => by rw [LocalizedFibreSets.fibLoc_eq_card]
  · push Not at hne
    obtain ⟨𝔭, h𝔭⟩ := hne
    have hE : fibG S L Λ' = ∅ := Set.eq_empty_of_forall_notMem fun Λ hΛ => by
      have h1 := LocalizedFibreSets.locF_mem_fibSet hK hF S hΛ 𝔭.2
      rw [h𝔭] at h1
      exact h1
    rw [hE, tprod_of_exists_eq_zero ⟨𝔭, by rw [LocalizedFibreSets.fibLoc_eq_card, h𝔭]; simp⟩]
    simp

end Formalism.HermitianLattices.Ext.L3
