import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSubFibreSubFib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

open LieTangent in

theorem valAt_eigen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] (zL : Sp L ⟶ 𝔐.X) (h : genPt 𝔐.ξ ⤳ centre zL) (g₀ : c.F →+* 𝔐.X.presheaf.stalk (centre zL)), (genMap 𝔐.ξ ⟨centre zL, h⟩).comp g₀ = 𝔐.cst → ∀ (s : CMType H ⊕ CMType H) (e : 𝔐.Li) (v : epsAt zL ⟶ 𝔐.t.G) (a : 𝓞 E), e ∈ 𝔐.Vgen s → 𝔐.M.ValAt zL e v → (v ≫ 𝔐.t.act.act a).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.epsMul ((Scheme.stalkClosedPointTo zL).hom (g₀ (labelEmb c s a))))) ≫ v.left := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 L _ zL h g₀ hg s e v a he hv
  obtain ⟨h', v₀, hext, rfl⟩ := (𝔐.M.valAt_iff zL e v).1 hv
  have hgen : genMap 𝔐.ξ ⟨centre zL, h⟩ (g₀ (labelEmb c s a)) = 𝔐.emb s a :=
    DFunLike.congr_fun hg (labelEmb c s a)
  have hρ : 𝔐.ρ a e = 𝔐.emb s a • e := by
    have h1 : e ∈ LinearMap.ker (𝔐.ρ a - 𝔐.emb s a • LinearMap.id) :=
      (Submodule.mem_iInf _).1 he a
    rw [LinearMap.mem_ker] at h1
    simpa [sub_eq_zero] using h1
  have hext' := (𝔐.M.extends_iff _ _ _).1 hext
  have h1 : 𝔐.M.Extends ⟨centre zL, h⟩ (𝔐.emb s a • e) (v₀ ≫ 𝔐.t.act.act a) := by
    rw [LieModel.extends_iff]
    refine ⟨?_, ?_⟩
    · rw [isTanAt_iff, ← Category.assoc, (isTanAt_iff _).1 hext'.1]
      haveI := 𝔐.t.act.hom a
      exact one_comp _
    · rw [← hρ, 𝔐.act a e, hext'.2, Category.assoc]
  have h2 := hext.smul (g₀ (labelEmb c s a))
  rw [hgen] at h2
  have key := h1.unique (𝔐.tie.gen.inj _) h2
  have e1 : epsBase _ (spec_centre zL) ≫ v₀ ≫ 𝔐.t.act.act a =
      epsScale zL ((Scheme.stalkClosedPointTo zL).hom (g₀ (labelEmb c s a))) ≫ epsBase _ (spec_centre zL) ≫ v₀ := by
    rw [key, ← Category.assoc, base_scale, Category.assoc]
    rfl
  exact congrArg (fun q => q.left) ((Category.assoc _ _ _).trans e1)

end GlobalTheory.CompanionTheory.Ar.FlagFib
