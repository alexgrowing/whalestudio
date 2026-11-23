import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NkCountEqSum
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoMeanAlphaN
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SumLocRepsEq

open NumberField Module Filter

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LIOrb

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {V' : Type} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V']
  [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem nu_gmap_locF (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) :
    nu h (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) 𝔭 = nu h L 𝔭 ∧
      vd h (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) 𝔭 = vd h L 𝔭 := by
  have hv : vd h (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) 𝔭 = vd h L 𝔭 := by
    rw [UnimodularLocalization.vd_gmap hg, vd_locF hK hF hs hd hL hLi h𝔭]
  have ha : alphaL h (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) 𝔭 = alphaL h L 𝔭 := by
    rw [BrB.alphaL_gmap hg]
    unfold alphaL
    simp only [akCount_locF hF h L 𝔭 h𝔭]
  refine ⟨?_, hv⟩
  unfold nu
  rw [ha, hv]

theorem main_term (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {M₂ : Submodule (𝓞 K) V} (hM₂ : Submodule.IsLattice K M₂)
    (hM₂i : Formalism.HermitianLatticesTheory.IsIntegralLat h M₂) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) (hx : h S.x₀ S.x₀ = algebraMap F K (n : F))
    (hx₂ : S.x₀ ∈ locF 𝔭 M₂)
    {s : Finset (Submodule (𝓞 K) V')} (hsr : IsLocReps S L 𝔭 s) :
    ∀ᶠ J in atTop, ∀ᶠ k in atTop,
      (nkCount h L 𝔭 k n : ℝ) = kap S (locF 𝔭 M₂) 𝔭 n J k *
        ((Ideal.absNorm 𝔭 : ℝ) ^ vd h L 𝔭 * nu h L 𝔭) *
        ∑ T ∈ s, (fibLoc S L 𝔭 T : ℝ) * (nu h' T 𝔭)⁻¹ := by
  obtain ⟨R, hR⟩ := exists_mReps hK hF hs hd S hL hLi h𝔭 hn hx hsr
  have h1 := nkCount_eq_sum hK hF hs hd S hL hLi h𝔭 hn hx hR
  have h2 : ∀ M ∈ R, ∀ᶠ J in atTop, ∀ᶠ k in atTop,
      kap S M 𝔭 n J k = kap S (locF 𝔭 M₂) 𝔭 n J k := by
    intro M hM
    obtain ⟨⟨⟨g, hg, rfl⟩, hxM⟩, -⟩ := hR.1 M hM
    rw [LocalizedFibreSets.gmap_locF] at hxM ⊢
    exact kap_eq hK hF hs hd S (LocalizedFibreSets.isLattice_gmap g hL) (UnimodularLocalization.isIntegralLat_gmap hg hLi) hM₂ hM₂i
      h𝔭 hn hx hxM hx₂
  have h3 : ∀ᶠ J in atTop, ∀ᶠ k in atTop, ∀ M ∈ R,
      kap S M 𝔭 n J k = kap S (locF 𝔭 M₂) 𝔭 n J k := by
    filter_upwards [(Finset.eventually_all R).mpr h2] with J hJ
    exact (Finset.eventually_all R).mpr hJ
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by
    exact_mod_cast reductionMapsOfForms.absNorm_pos h𝔭
  filter_upwards [h1, h3] with J hJ1 hJ3
  filter_upwards [hJ1, hJ3] with k hk1 hk3
  rw [hk1, ← sum_oM hK hF hs hd S hL hLi h𝔭 hsr hR (fun T => (nu h' T 𝔭)⁻¹), Nat.cast_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun M hM => ?_
  rw [← hk3 M hM]
  obtain ⟨⟨⟨g, hg, rfl⟩, hxM⟩, -⟩ := hR.1 M hM
  obtain ⟨e1, e2⟩ := nu_gmap_locF hK hF hs hd hL hLi h𝔭 hg
  have hν : 0 < nu h L 𝔭 := by
    rw [← e1, LocalizedFibreSets.gmap_locF]
    exact nu_pos hK hF hs hd (LocalizedFibreSets.isLattice_gmap g hL) (UnimodularLocalization.isIntegralLat_gmap hg hLi) h𝔭
  have hν' : 0 < nu h' (S.cut (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L))) 𝔭 := by
    rw [LocalizedFibreSets.gmap_locF, LocalizedFibreSets.cut_locF]
    exact nu_pos hK hF (S.isSymm hs) (S.isTotPosDef hd)
      (StabilizerLattices.isLattice_cut S (LocalizedFibreSets.isLattice_gmap g hL))
      (UnimodularLocalization.isIntegralLat_cut S (UnimodularLocalization.isIntegralLat_gmap hg hLi)) h𝔭
  have ho : (oM S (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) : ℝ) ≠ 0 := by
    rw [LocalizedFibreSets.gmap_locF] at hxM ⊢
    exact_mod_cast oM_ne_zero hs S (LocalizedFibreSets.isLattice_gmap g hL) h𝔭 hxM
  unfold kap
  rw [e1, e2]
  have hq' := pow_pos hq (vd h L 𝔭)
  field_simp

end Formalism.HermitianLattices.Ext.L3.LIOrb
