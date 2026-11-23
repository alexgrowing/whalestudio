import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem restrict_proper_sections_bijective_to_fibre_open : ∀ (Y₀ H X'' P'' : Scheme.{0}) (H' : H.Opens) (i : H'.toScheme ⟶ X'') (a'' : X'' ⟶ P'') (b'' : P'' ⟶ Y₀), IsNoetherian Y₀ → IsOpenImmersion i → IsProper a'' → Surjective a'' → (∀ V : P''.Opens, Function.Bijective (a''.app V).hom) → IsFinite b'' → ∃ (P' : Scheme.{0}) (c : P' ⟶ P'') (X : H.Opens) (k : X.toScheme ⟶ H'.toScheme) (a : X.toScheme ⟶ P'), IsOpenImmersion c ∧ IsNoetherian P' ∧ IsProper a ∧ Surjective a ∧ (∀ V : P'.Opens, Function.Bijective (a.app V).hom) ∧ k ≫ H'.ι = X.ι ∧ a ≫ c = k ≫ i ≫ a'' ∧ (∀ z : H'.toScheme, (∀ w : X'', a'' w = a'' (i z) → w ∈ Set.range i) → H'.ι z ∈ X) ∧ ∀ w : X'', a'' w ∈ Set.range c → w ∈ Set.range (k ≫ i) := by
  intro Y₀ H X'' P'' H' i a'' b'' hY hi ha hs hV hb
  haveI := hY; haveI := hi; haveI := ha; haveI := hs; haveI := hb
  have hP : IsNoetherian P'' := by
    haveI : IsLocallyNoetherian P'' := LocallyOfFiniteType.isLocallyNoetherian b''
    haveI : CompactSpace P'' := QuasiCompact.compactSpace_of_compactSpace b''
    exact {}
  let U0 : P''.Opens := ⟨(a'' '' (Set.range i)ᶜ)ᶜ,
    (a''.isClosedMap _ i.isOpenEmbedding.isOpen_range.isClosed_compl).isOpen_compl⟩
  have hsub : ∀ w : X'', a'' w ∈ U0 → w ∈ Set.range i := by
    intro w hw
    by_contra h
    exact hw ⟨w, h, rfl⟩
  let W : H'.toScheme.Opens := i ⁻¹ᵁ (a'' ⁻¹ᵁ U0)
  let X : H.Opens := H'.ι ''ᵁ W
  have hXr : Set.range X.ι ⊆ Set.range H'.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, -, rfl⟩
    exact ⟨z, rfl⟩
  let k : X.toScheme ⟶ H'.toScheme := IsOpenImmersion.lift H'.ι X.ι hXr
  have hk : k ≫ H'.ι = X.ι := IsOpenImmersion.lift_fac _ _ _
  have hrk : Set.range k = (W : Set H'.toScheme) := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      have h1 : H'.ι (k y) ∈ X := by
        rw [← Scheme.Hom.comp_apply, hk]
        have : X.ι y ∈ Set.range X.ι := ⟨y, rfl⟩
        rwa [Scheme.Opens.range_ι] at this
      obtain ⟨w, hw, he⟩ := h1
      rwa [← H'.ι.isOpenEmbedding.injective he]
    · intro hz
      have : H'.ι z ∈ Set.range X.ι := by
        rw [Scheme.Opens.range_ι]; exact ⟨z, hz, rfl⟩
      obtain ⟨y, hy⟩ := this
      refine ⟨y, H'.ι.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, hk, hy]
  have hrki : Set.range (k ≫ i) = (a'' ⁻¹ᵁ U0 : Set X'') := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrk]
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩; exact hz
    · intro hw
      obtain ⟨z, rfl⟩ := hsub w hw
      exact ⟨z, hw, rfl⟩
  let e := IsOpenImmersion.isoOfRangeEq (k ≫ i) (a'' ⁻¹ᵁ U0).ι (by rw [Scheme.Opens.range_ι]; exact hrki)
  let a : X.toScheme ⟶ U0.toScheme := e.hom ≫ (a'' ∣_ U0)
  have hfac : a ≫ U0.ι = k ≫ i ≫ a'' := by
    simp only [a, e, Category.assoc, morphismRestrict_ι, IsOpenImmersion.isoOfRangeEq_hom_fac_assoc]
  refine ⟨U0.toScheme, U0.ι, X, k, a, inferInstance, ?_, inferInstance, ?_, ?_, hk, hfac, ?_, ?_⟩
  · haveI := hP
    haveI : CompactSpace U0.toScheme := QuasiCompact.compactSpace_of_compactSpace U0.ι
    exact {}
  · refine ⟨fun x => ?_⟩
    obtain ⟨w, hw⟩ := a''.surjective x.1
    have hw' : w ∈ Set.range (k ≫ i) := by
      rw [hrki]; show a'' w ∈ U0; rw [hw]; exact x.2
    obtain ⟨y, rfl⟩ := hw'
    refine ⟨y, U0.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hfac]
    simp only [Scheme.Hom.comp_apply] at hw ⊢
    rw [hw]; rfl
  · intro V
    show Function.Bijective ((e.hom ≫ (a'' ∣_ U0)).app V).hom
    rw [Scheme.Hom.comp_app]
    have h1 : Function.Bijective ((a'' ∣_ U0).app V).hom := by
      rw [morphismRestrict_app]
      have h3 := hV (U0.ι ''ᵁ V)
      have h4 : Function.Bijective (X''.presheaf.map (eqToHom (image_morphismRestrict_preimage a'' U0 V)).op).hom :=
        ConcreteCategory.bijective_of_isIso _
      exact h4.comp h3
    have h2 : Function.Bijective (e.hom.app ((a'' ∣_ U0) ⁻¹ᵁ V)).hom := ConcreteCategory.bijective_of_isIso _
    exact h2.comp h1
  · intro z hz
    have : z ∈ W := by
      show a'' (i z) ∈ U0
      rintro ⟨w, hw, he⟩
      exact hw (hz w he)
    exact ⟨z, this, rfl⟩
  · intro w hw
    rw [hrki]
    rw [Scheme.Opens.range_ι] at hw
    exact hw

end GlobalTheory
