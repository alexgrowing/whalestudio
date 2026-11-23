import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction

noncomputable section

open CategoryTheory

namespace UpperTheory.V.Lit.Dr

theorem acyclic : Acyclic := by
  intro Γ Ω _ _ _ ρ hP n
  obtain ⟨P, hconst, hequi⟩ := hP
  let S : Subgroup Γ := ⊥
  haveI : Subsingleton S := ⟨fun a b => Subtype.ext ((Subgroup.mem_bot.1 a.2).trans (Subgroup.mem_bot.1 b.2).symm)⟩
  let A : Rep ℂ S := Rep.of (Representation.trivial ℂ S Ω)
  let C : Rep ℂ Γ := Rep.coind S.subtype A
  have hC : Subsingleton (groupCohomology C (n + 1)) := by
    have hz : Limits.IsZero (groupCohomology C (n + 1)) :=
      (isZero_groupCohomology_succ_of_subsingleton A n).of_iso (groupCohomology.coindIso A (n + 1))
    have h0 : 𝟙 (groupCohomology C (n + 1)) = 0 := hz.eq_of_src _ _
    refine ⟨fun a b => ?_⟩
    have ha := congrArg (fun f => f.hom a) h0
    have hb := congrArg (fun f => f.hom b) h0
    simp only [ModuleCat.hom_id, ModuleCat.hom_zero, LinearMap.id_apply, LinearMap.zero_apply] at ha hb
    rw [ha, hb]
  let L : Ω →ₗ[ℂ] (Γ → Ω) := LinearMap.pi fun h => ρ h
  have hL : ∀ x, L x ∈ Representation.coindV S.subtype A.ρ := by
    intro x g h
    have hg : (g : Γ) = 1 := Subgroup.mem_bot.1 g.2
    simp [L, hg]
  let iL : Ω →ₗ[ℂ] Representation.coindV S.subtype A.ρ := LinearMap.codRestrict _ L hL
  let M : Representation.coindV S.subtype A.ρ →ₗ[ℂ] (Γ → Ω) :=
    LinearMap.pi fun g => ρ g ∘ₗ LinearMap.proj g⁻¹ ∘ₗ Submodule.subtype _
  let rL : Representation.coindV S.subtype A.ρ →ₗ[ℂ] Ω := P ∘ₗ M
  let i : Rep.of ρ ⟶ C := Rep.ofHom ⟨iL, fun γ => by
    refine LinearMap.ext fun x => Subtype.ext (funext fun h => ?_)
    simp only [iL, L, LinearMap.comp_apply]
    show (ρ h) ((ρ γ) x) = (ρ (h * γ)) x
    rw [map_mul, Module.End.mul_apply]⟩
  let r : C ⟶ Rep.of ρ := Rep.ofHom ⟨rL, fun γ => by
    refine LinearMap.ext fun f => ?_
    simp only [LinearMap.comp_apply, rL, M]
    rw [hequi]
    congr 1
    funext g
    simp [mul_inv_rev, ← Module.End.mul_apply, ← map_mul]
    rfl⟩
  have hri : i ≫ r = 𝟙 _ := by
    ext x
    simp [i, r, rL, M, iL, L, ← Module.End.mul_apply, ← map_mul, hconst]
    show P (fun g => ρ g (ρ g⁻¹ x)) = x
    rw [show (fun g => ρ g (ρ g⁻¹ x)) = fun _ => x from
      funext fun g => by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply], hconst]
  let F := groupCohomology.functor ℂ Γ (n + 1)
  have hinj : Function.Injective (F.map i).hom := by
    intro a b hab
    have key : ∀ z, (F.map r).hom ((F.map i).hom z) = z := by
      intro z
      rw [← ModuleCat.comp_apply, ← F.map_comp, hri, F.map_id]
      rfl
    rw [← key a, ← key b, hab]
  haveI : Subsingleton (F.obj C) := hC
  exact hinj.subsingleton

end UpperTheory.V.Lit.Dr
