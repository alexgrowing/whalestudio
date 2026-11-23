import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLatticeOfFibLocNeZeroGood
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardFibGEqProd

open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.GoodPrimeTerms

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

open UnimodularLocalization

theorem good_term (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : h S.x₀ S.x₀ = algebraMap F K (n : F))
    (hvL : vd h L 𝔭 = 0) (hvn : vF 𝔭 n = 0) {T : Submodule (𝓞 K) V'} (hTl : locF 𝔭 T = T)
    (hT : fibLoc S L 𝔭 T ≠ 0) : fibLoc S L 𝔭 T = 1 ∧ lamP h' T 𝔭 = 1 := by
  obtain ⟨C, hC, hCi, hvC, e⟩ :=
    exists_lattice_of_fibLoc_ne_zero_good hK hF hs hd S hL hLi h𝔭 hn hvL hvn hT
  constructor
  · rw [← fibLoc_congr S L e]
    exact fibLoc_eq_one hK hF hs hd S hL hLi hC hCi h𝔭 hn hvL hvn hvC
  · rw [← hTl, ← e, localFactor_localField hK hF (S.isSymm hs) (S.isTotPosDef hd) hC hCi h𝔭]
    exact localMassFactor_of_valuation_eq_zero hK hF (S.isSymm hs) (S.isTotPosDef hd) hC hCi h𝔭 hvC

theorem good_orbit (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : h S.x₀ S.x₀ = algebraMap F K (n : F))
    (hvL : vd h L 𝔭 = 0) (hvn : vF 𝔭 n = 0) {T T' : Submodule (𝓞 K) V'}
    (hT : fibLoc S L 𝔭 T ≠ 0) (hT' : fibLoc S L 𝔭 T' ≠ 0) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 T) = locF 𝔭 T' := by
  obtain ⟨C, hC, hCi, hvC, e⟩ :=
    exists_lattice_of_fibLoc_ne_zero_good hK hF hs hd S hL hLi h𝔭 hn hvL hvn hT
  obtain ⟨C', hC', hCi', hvC', e'⟩ :=
    exists_lattice_of_fibLoc_ne_zero_good hK hF hs hd S hL hLi h𝔭 hn hvL hvn hT'
  rw [← e, ← e']
  exact exists_isom_locF_of_vd_zero hK hF (S.isSymm hs) (S.isTotPosDef hd) hC hC' hCi hCi' h𝔭
    hvC hvC'

theorem isIntegralAt_locF {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] {h₀ : W →ₗ⋆[K] W →ₗ[K] K} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsPrime)
    (hF : IsFixF K F) {C : Submodule (𝓞 K) W}
    (hCi : Formalism.HermitianLatticesTheory.IsIntegralLat h₀ C) : IsIntegralAt 𝔭 h₀ (locF 𝔭 C) := by
  intro x hx y hy
  obtain ⟨s, hs, hx⟩ := (LocF.mem_locF_iff h𝔭 _ _).mp hx
  obtain ⟨t, ht, hy⟩ := (LocF.mem_locF_iff h𝔭 _ _).mp hy
  refine (LocF.mem_locF_iff h𝔭 _ _).mpr ⟨s * t, fun e => (h𝔭.mem_or_mem e).elim hs ht, ?_⟩
  have h1 := hCi _ hx _ hy
  have e : conjO K (algebraMap (𝓞 F) (𝓞 K) s) = algebraMap (𝓞 F) (𝓞 K) s :=
    (conjO_eq_iff_mem_range hF _).mpr ⟨s, rfl⟩
  have h2 : h₀ (algebraMap (𝓞 F) (𝓞 K) s • x) (algebraMap (𝓞 F) (𝓞 K) t • y) =
      (conjO K (algebraMap (𝓞 F) (𝓞 K) s) * algebraMap (𝓞 F) (𝓞 K) t) • h₀ x y := by
    have e' : algebraMap (𝓞 K) K (conjO K (algebraMap (𝓞 F) (𝓞 K) s)) =
      starRingEnd K (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) s)) := rfl
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) s) x,
      ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) y, map_smul, map_smulₛₗ,
      LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, Algebra.smul_def, map_mul, e']
    ring
  rw [h2, e, ← map_mul] at h1
  exact h1

theorem psiP_eq_one' (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : h S.x₀ S.x₀ = algebraMap F K (n : F))
    (hvL : vd h L 𝔭 = 0) (hvn : vF 𝔭 n = 0) : psiP S L 𝔭 = 1 := by
  classical
  obtain ⟨C, hC, hCi, hvC⟩ := exists_unimod_lattice_good hK hF hs hd S hL hLi h𝔭 hn hvL hvn
  have hfC : fibLoc S L 𝔭 (locF 𝔭 C) ≠ 0 := by
    rw [fibLoc_locF, fibLoc_eq_one hK hF hs hd S hL hLi hC hCi h𝔭 hn hvL hvn hvC]
    exact one_ne_zero
  have hex : ∃ s, IsLocReps S L 𝔭 s := by
    refine ⟨{locF 𝔭 C}, ?_, ?_⟩
    · intro T hT
      rw [Finset.mem_singleton] at hT
      subst hT
      exact ⟨LocF.locF_idem _ _, isIntegralAt_locF h𝔭.isPrime hF hCi, hfC⟩
    · intro T hTl _ hT
      obtain ⟨g, hg, e⟩ := good_orbit hK hF hs hd S hL hLi h𝔭 hn hvL hvn hfC hT
      rw [LocF.locF_idem, hTl] at e
      refine ⟨locF 𝔭 C, ⟨Finset.mem_singleton_self _, g, hg, e⟩, ?_⟩
      rintro T₀ ⟨h1, -⟩
      exact Finset.mem_singleton.mp h1
  unfold psiP
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  set s := hex.choose
  obtain ⟨T₀, ⟨hT₀, -⟩, -⟩ := h2 (locF 𝔭 C) (LocF.locF_idem _ _)
    (isIntegralAt_locF h𝔭.isPrime hF hCi) hfC
  have hs1 : s = {T₀} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    refine ⟨hT₀, fun T hT => ?_⟩
    obtain ⟨g, hg, e⟩ := good_orbit hK hF hs hd S hL hLi h𝔭 hn hvL hvn (h1 T hT).2.2
      (h1 T₀ hT₀).2.2
    rw [(h1 T hT).1, (h1 T₀ hT₀).1] at e
    obtain ⟨T₁, -, hu⟩ := h2 T₀ (h1 T₀ hT₀).1 (h1 T₀ hT₀).2.1 (h1 T₀ hT₀).2.2
    rw [hu T ⟨hT, g, hg, e⟩, hu T₀ ⟨hT₀, 1, Subgroup.one_mem _, autSub_gmap_one _⟩]
  obtain ⟨e1, e2⟩ := good_term hK hF hs hd S hL hLi h𝔭 hn hvL hvn (h1 T₀ hT₀).1 (h1 T₀ hT₀).2.2
  rw [hs1, Finset.sum_singleton, e1, e2]
  simp

end Formalism.HermitianLattices.Ext.L3.GoodPrimeTerms
