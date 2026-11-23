import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Factor
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.SecSpec

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

theorem UpperTheory.V.Z.Sym.Al.isoTypic :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : Submodule ℂ (UA L n → ℂ)) (hπ : IsAutRepU π) (w : Plc L), IsSplitAt w → ∀ τ, Comp π w τ →
        (⨆ f : {f : τ.V →ₗ[ℂ] π // ∀ h x, f (τ.ρ h x) = (repOn hπ).comp (secW n w) h (f x)}, LinearMap.range f.1) = ⊤ := by
  intro L _ _ _ n π hπ w hw τ ⟨_, f, f0, fm, fe⟩
  obtain ⟨f1, f2, -⟩ := factor L n w
  obtain ⟨s1, s2, s3, -⟩ := secSpec L n w hw
  set N := ⨆ f : {f : τ.V →ₗ[ℂ] π // ∀ h x, f (τ.ρ h x) = (repOn hπ).comp (secW n w) h (f x)}, LinearMap.range f.1 with hN
  have hst : ∀ g, ∀ v ∈ N, repOn hπ g v ∈ N := by
    intro g v hv
    obtain ⟨x, hx, y, hy, rfl⟩ := f2 g
    refine Submodule.iSup_induction _ (motive := fun v => repOn hπ (x * y) v ∈ N) hv ?_ (by simp) fun a b ha hb => by
      rw [map_add]; exact N.add_mem ha hb
    rintro ⟨p, hp⟩ _ ⟨t, rfl⟩
    refine Submodule.mem_iSup_of_mem ⟨repOn hπ y ∘ₗ p, fun h t => ?_⟩ ⟨τ.ρ (cLoc w x) t, ?_⟩
    · rw [LinearMap.comp_apply, hp, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, ← f1 _ (s1 h) y hy, map_mul]; rfl
    · rw [LinearMap.comp_apply, hp, MonoidHom.comp_apply, s3 x hx, ← Module.End.mul_apply, ← map_mul, f1 x hx y hy]
  rcases hπ.irred (N.map π.subtype) (Submodule.map_subtype_le _ _) (by
    rintro x _ ⟨v, hv, rfl⟩
    exact ⟨_, hst x v hv, rfl⟩) with h | h
  · refine absurd (LinearMap.ext fun t => ?_) f0
    have : f t ∈ N.map π.subtype := ⟨⟨f t, fm t⟩, Submodule.mem_iSup_of_mem ⟨f.codRestrict π fm, fun h t => Subtype.ext (by
      have := fe ⟨secW n w h, s1 h⟩ t
      rw [MonoidHom.comp_apply, Subgroup.subtype_apply, s2] at this
      exact this)⟩ ⟨t, rfl⟩, rfl⟩
    rwa [h] at this
  · exact Submodule.map_injective_of_injective π.injective_subtype (by rw [h, Submodule.map_subtype_top])
