import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FormRightMem
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardEqRelIndex

open NumberField Module Filter

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LIOrb

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem card_quot_inf_ne_zero {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsLattice K M₁)
    (hM₂ : Submodule.IsLattice K M₂) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    Nat.card (↥(locF 𝔭 M₁) ⧸ (locF 𝔭 M₁ ⊓ locF 𝔭 M₂).submoduleOf (locF 𝔭 M₁)) ≠ 0 := by
  obtain ⟨r, hr⟩ := IA.exists_pow_smul h𝔭 hM₁ hM₂
  rw [IA.card_eq_relIndex h𝔭 hr]
  exact IA.relIndex_ne_zero hM₁ hM₂ 𝔭

private theorem isLattice_inf_locF_of_isLattice {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {M N : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M) (hN : Submodule.IsLattice K N) :
    Submodule.IsLattice K (M ⊓ locF 𝔭 N) := by
  obtain ⟨r, hr⟩ := IA.exists_pow_smul h𝔭 hM hN
  have h0 : 𝔭 ≠ ⊥ := fun h0 =>
    NumberField.RingOfIntegers.not_isField F (Ring.isField_iff_maximal_bot.2 (h0 ▸ h𝔭))
  have hne : 𝔭 ^ r ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot] at h0 ⊢
    exact pow_ne_zero r h0
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  set c : K := algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a) with hc_def
  have hc : c ≠ 0 := by
    intro hc0
    apply ha0
    apply NumberField.RingOfIntegers.algebraMap.injective F K
    apply NumberField.RingOfIntegers.coe_injective (K := K)
    simpa [hc_def] using hc0
  refine ⟨?_, ?_⟩
  · have := hM
    have : IsNoetherian (𝓞 K) ↥(M ⊓ locF 𝔭 N) := isNoetherian_of_le inf_le_left
    rw [← Module.Finite.iff_fg]
    infer_instance
  · rw [eq_top_iff, ← hM.2, Submodule.span_le]
    intro y hy
    have hmem : algebraMap (𝓞 F) (𝓞 K) a • y ∈ M ⊓ locF 𝔭 N := ⟨M.smul_mem _ hy, hr a ha y hy⟩
    have ey : y = c⁻¹ • (algebraMap (𝓞 F) (𝓞 K) a • y) := by
      rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) a) y, ← hc_def, smul_smul, inv_mul_cancel₀ hc,
        one_smul]
    rw [SetLike.mem_coe, ey]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem card_quot_inf_mul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsLattice K M₁)
    (hM₁i : Formalism.HermitianLatticesTheory.IsIntegralLat h M₁) (hM₂ : Submodule.IsLattice K M₂)
    (hM₂i : Formalism.HermitianLatticesTheory.IsIntegralLat h M₂) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    Nat.card (↥(locF 𝔭 M₁) ⧸ (locF 𝔭 M₁ ⊓ locF 𝔭 M₂).submoduleOf (locF 𝔭 M₁)) *
        Ideal.absNorm 𝔭 ^ vd h (locF 𝔭 M₁) 𝔭 =
      Nat.card (↥(locF 𝔭 M₂) ⧸ (locF 𝔭 M₁ ⊓ locF 𝔭 M₂).submoduleOf (locF 𝔭 M₂)) *
        Ideal.absNorm 𝔭 ^ vd h (locF 𝔭 M₂) 𝔭 := by
  obtain ⟨r₁, hr₁⟩ := IA.exists_pow_smul h𝔭 hM₁ hM₂
  obtain ⟨r₂, hr₂⟩ := IA.exists_pow_smul h𝔭 hM₂ hM₁
  have e₁ := IA.card_eq_relIndex h𝔭 hr₁
  have e₂ := IA.card_eq_relIndex h𝔭 hr₂
  rw [inf_comm (locF 𝔭 M₂) (locF 𝔭 M₁)] at e₂

  have hAi : Formalism.HermitianLatticesTheory.IsIntegralLat h (M₁ ⊓ locF 𝔭 M₂) := fun x hx y hy => hM₁i x hx.1 y hy.1
  have hBi : Formalism.HermitianLatticesTheory.IsIntegralLat h (M₂ ⊓ locF 𝔭 M₁) := fun x hx y hy => hM₂i x hx.1 y hy.1
  have hvA := vd_locF hK hF hs hd (isLattice_inf_locF_of_isLattice h𝔭 hM₁ hM₂) hAi h𝔭
  have hvB := vd_locF hK hF hs hd (isLattice_inf_locF_of_isLattice h𝔭 hM₂ hM₁) hBi h𝔭
  rw [IA.locF_inf 𝔭 h𝔭.isPrime] at hvA hvB
  have hAB : vd h (M₁ ⊓ locF 𝔭 M₂) 𝔭 = vd h (M₂ ⊓ locF 𝔭 M₁) 𝔭 := by
    rw [← hvA, ← hvB, inf_comm]
  rw [e₁, e₂, vd_locF hK hF hs hd hM₁ hM₁i h𝔭, vd_locF hK hF hs hd hM₂ hM₂i h𝔭,
    IA.vd_mul hF hK hs hd hM₁ hM₁i hM₂ h𝔭, IA.vd_mul hF hK hs hd hM₂ hM₂i hM₁ h𝔭, hAB]

end Formalism.HermitianLattices.Ext.L3.LIOrb
