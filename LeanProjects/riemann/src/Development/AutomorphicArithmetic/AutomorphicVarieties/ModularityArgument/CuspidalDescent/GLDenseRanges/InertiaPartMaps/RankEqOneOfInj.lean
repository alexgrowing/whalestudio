import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.KirCusp

open UpperTheory.V.Z.Desc.V0

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.V.Z.Desc.V0.rank_eq_one_of_inj {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Submodule ℂ W) (l : W →ₗ[ℂ] ℂ) (hne : S ≠ ⊥) (hinj : ∀ v ∈ S, l v = 0 → v = 0) :
    Module.rank ℂ ↥S = 1 := by
  have hle : Module.rank ℂ ↥S ≤ 1 := by
    have hi : Function.Injective (l ∘ₗ S.subtype) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      have := hinj v.1 v.2 hv
      exact Subtype.ext this
    simpa using LinearMap.rank_le_of_injective _ hi
  have hne0 : Module.rank ℂ ↥S ≠ 0 := by
    rw [Ne, Submodule.rank_eq_zero]
    exact hne
  exact le_antisymm hle (Cardinal.one_le_iff_ne_zero.mpr hne0)

theorem UpperTheory.V.Z.Desc.V0.locE :
    KirMove → IsoNe → IsoLe → EOp → LocE := by
  intro hMove hNe hLe hE k _ _ _ _ n
  obtain ⟨ψ, a, j, T, hψ, hIsE, hTne, hTval, hrank⟩ := hE k n
  refine ⟨a, j, T.card, hIsE, Finset.card_pos.mpr hTne, ?_⟩
  intro W _ _ τ hsm hKir hfix
  have hψne : ψ ≠ 1 := by
    rintro rfl
    obtain ⟨_, _, x, _, hx⟩ := hψ
    exact hx (AddChar.one_apply x)
  have hone : ∀ t ∈ T, Module.rank ℂ ↥(isoPart τ ψ t) = 1 := by
    intro t ht
    have ht0 : ∀ i, t i ≠ 0 := by
      intro i h
      have := hTval t ht i
      rw [h, map_zero] at this
      exact zero_ne_one this
    obtain ⟨l, hl⟩ := hMove k n W τ hKir ψ t hψ.1 hψne ht0
    exact UpperTheory.V.Z.Desc.V0.rank_eq_one_of_inj _ l
      (hNe k n W τ hsm ψ t l hψ (hTval t ht) hl hfix)
      (hLe k n W τ ψ t l hψ (hTval t ht) hl)
  rw [hrank W τ, Finset.sum_congr rfl hone]
  simp
