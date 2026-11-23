import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTraitNonlocalTorusExtensionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendSplitTorusHomOverDvrStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationTorusMonoAndFactor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.SpreadTrait

theorem pull_cancel {S S' S'' : Scheme.{0}} {G : Over S} [GrpObj G] {G₁ : Over S'} [GrpObj G₁] {f : S' ⟶ S}
    {m₁ : G₁.left ⟶ G.left} (h₁ : IsGrpPullback G₁ G f m₁) (u : S'' ⟶ S') {Gl : Over S''} [GrpObj Gl]
    {φl : Gl.left ⟶ G.left} (hGl : IsGrpPullback Gl G (u ≫ f) φl) :
    ∃ φ : Gl.left ⟶ G₁.left, IsGrpPullback Gl G₁ u φ ∧ φ ≫ m₁ = φl :=
  ⟨h₁.1.lift φl (Gl.hom ≫ u) (by rw [hGl.1.w, Category.assoc]),
    h₁.cancel (hGl.congr rfl (h₁.1.lift_fst _ _ _).symm) (h₁.1.lift_snd _ _ _), h₁.1.lift_fst _ _ _⟩

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (u : A →+* B) (v : B →+* C) :
    spMap v ≫ spMap u = spMap (v.comp u) := (Spec.map_comp _ _).symm

theorem spread_of_trait {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {D' : DegData V (maximalIdeal V)}
    {A' : PolAV (Sp (FractionRing V))} {G' : Over (Sp V)} [GrpObj G'] [IsCommMonObj G']
    (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left)
    (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsDiscreteValuationRing V₁] (ψ : R →+* V₁) (hψ : IsLocalHom ψ)
    (Ω : Type) [Field Ω] (α : V₁ →+* Ω) (hα : Function.Injective α) (b : V →+* Ω)
    (hb : ∀ x ∈ maximalIdeal V ^ (0 + 1), b x = 0) (eα : α.comp ψ = b.comp g)
    (GΩ : Over (Sp Ω)) [GrpObj GΩ] (n : GΩ.left ⟶ ((Over.pullback (spMap ψ)).obj G).left)
    (hn : IsGrpPullback GΩ ((Over.pullback (spMap ψ)).obj G) (spMap α) n)
    (n' : GΩ.left ⟶ G'.left) (hn' : IsGrpPullback GΩ G' (spMap b) n')
    (hnn : n ≫ pullback.fst G.hom (spMap ψ) = n' ≫ β)
    (j : splitTorus (Sp V₁) D'.toPre.X ⟶ (Over.pullback (spMap ψ)).obj G) (hj : IsMonHom j)
    (ej : GlobalTheory.TorusPart.pullTorus hn j = GlobalTheory.TorusPart.gtTorus (U'.gt 0) hb hn') :
    ∃ ρ, Spread U U' g β ρ := by
  haveI := hψ
  haveI := hj
  have hm₁ := isGrpPullback_pullback G (spMap ψ)
  have hm₀ := isGrpPullback_pullback ((Over.pullback (spMap ψ)).obj G) (spMap (residue V₁))
  have hm₀' := (hm₀.comp hm₁).congr (spMap_comp' ψ (residue V₁)) rfl
  have h₀ : ∀ x ∈ maximalIdeal R, (residue V₁).comp ψ x = 0 := GlobalTheory.TorusPart.map_eq_zero_of_isLocalHom _
  obtain ⟨ρ, hρ⟩ := (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U.gt 0) (GlobalTheory.TorusPart.map_pow_one_eq_zero h₀)
    hm₀').2 _ (GlobalTheory.TorusPart.pullTorus hm₀ j) inferInstance
  exact ⟨ρ, V₁, inferInstance, inferInstance, inferInstance, ψ, (Over.pullback (spMap ψ)).obj G, inferInstance,
    inferInstance, pullback.fst G.hom (spMap ψ), Ω, inferInstance, α, b, hb, GΩ, inferInstance, n, hn, n', hn', j, _,
    inferInstance, _, hm₀, GlobalTheory.TorusPart.map_pow_one_eq_zero h₀, hm₀', hψ, hm₁, hj, hα, eα, hnn, ej, hρ⟩

theorem exists_spread : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left), IsGrpPullback G' G (spMap g) β → ∃ ρ, Spread U U' g β ρ := by
  intro R _ _ _ hR G _ _ hG D A U V _ _ _ hV G' _ _ hG' D' A' U' g β hβ
  haveI : IsNoetherianRing R := hR.1.1
  by_cases hl : IsLocalHom g
  · haveI := hl
    let κ := ResidueField V
    have hC : IsLocalHom (PowerSeries.C (R := κ)) :=
      ⟨fun a ha => by simpa using ha.map (PowerSeries.constantCoeff (R := κ))⟩
    let c : V →+* PowerSeries κ := (PowerSeries.C (R := κ)).comp (residue V)
    have hcl : IsLocalHom c := RingHom.isLocalHom_comp _ _
    let ψ : R →+* PowerSeries κ := c.comp g
    have hψ : IsLocalHom ψ := RingHom.isLocalHom_comp _ _
    let α := algebraMap (PowerSeries κ) (FractionRing (PowerSeries κ))
    have hα : Function.Injective α := IsFractionRing.injective _ _
    let b : V →+* FractionRing (PowerSeries κ) := α.comp c
    have hc0 : ∀ x ∈ maximalIdeal V, c x = 0 := fun x hx => by
      simp [c, (IsLocalRing.residue_eq_zero_iff x).2 hx]
    have hc : ∀ x ∈ maximalIdeal V ^ (0 + 1), c x = 0 := GlobalTheory.TorusPart.map_pow_one_eq_zero hc0
    have hb : ∀ x ∈ maximalIdeal V ^ (0 + 1), b x = 0 := fun x hx => by
      simp [b, hc x hx]
    have hm₁ := isGrpPullback_pullback G (spMap ψ)
    obtain ⟨mc, hmc, hmcβ⟩ := pull_cancel hβ (spMap c) (hm₁.congr (spMap_comp' g c).symm rfl)
    have hn := isGrpPullback_pullback ((Over.pullback (spMap ψ)).obj G) (spMap α)
    have hn' : IsGrpPullback _ G' (spMap b) _ := (hn.comp hmc).congr (spMap_comp' c α) rfl
    have hnn : pullback.fst ((Over.pullback (spMap ψ)).obj G).hom (spMap α) ≫ pullback.fst G.hom (spMap ψ) =
        (pullback.fst ((Over.pullback (spMap ψ)).obj G).hom (spMap α) ≫ mc) ≫ β := by
      rw [Category.assoc, hmcβ]
    exact spread_of_trait U U' g β (PowerSeries κ) ψ hψ _ α hα b hb rfl _ _ hn _ hn' hnn
      (GlobalTheory.TorusPart.gtTorus (U'.gt 0) hc hmc) inferInstance
      (GlobalTheory.TorusPart.pullTorus_gtTorus (U'.gt 0) hc hb hmc hn' hn rfl rfl)
  · obtain ⟨V₁, _, _, _, ψ, Ω, _, αK, b, hψ, hb, eα, hT⟩ := GlobalTheory.T.exists_trait_nonlocal_torusExtension' R G hG V g hl
    haveI := hψ
    let alg := algebraMap V₁ (FractionRing V₁)
    have hα : Function.Injective (αK.comp alg) :=
      αK.injective.comp (IsFractionRing.injective V₁ (FractionRing V₁))
    have hm₁ := isGrpPullback_pullback G (spMap ψ)
    have hG₁ : IsSemiAbelian ((Over.pullback (spMap ψ)).obj G) := IsSemiAbelian.pullback _ G hG
    obtain ⟨φ₁, hφ₁, -⟩ := pull_cancel hm₁ (spMap alg)
      ((isGrpPullback_pullback G (spMap (alg.comp ψ))).congr (spMap_comp' ψ alg).symm rfl)
    have hn' := isGrpPullback_pullback G' (spMap b)
    obtain ⟨n, hn, hnm⟩ := pull_cancel hm₁ (spMap (αK.comp alg))
      ((hn'.comp hβ).congr ((spMap_comp' g b).trans ((congrArg spMap eα.symm).trans
        (spMap_comp' ψ (αK.comp alg)).symm)) rfl)
    have hb' : ∀ x ∈ maximalIdeal V ^ (0 + 1), b x = 0 := GlobalTheory.TorusPart.map_pow_one_eq_zero hb
    obtain ⟨j, hj, ej⟩ := GlobalTheory.T.extend_splitTorus_hom_over_dvr V₁ ((Over.pullback (spMap ψ)).obj G) hG₁ _ φ₁ hφ₁ hT Ω αK _ n hn _
      (GlobalTheory.TorusPart.gtTorus (U'.gt 0) hb' hn') inferInstance
    exact spread_of_trait U U' g β V₁ ψ hψ Ω (αK.comp alg) hα b hb' eα _ n hn _ hn' hnm j hj ej

end GlobalTheory.SpreadTrait
