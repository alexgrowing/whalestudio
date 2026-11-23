import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoNearNormalPointOfFiniteBirational
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MorphismExtensionFromGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpecMorphismEqOfLocalInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDominantGenericStalkOpenStatement
open AlgebraicGeometry CategoryTheory Limits IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.TorRef

namespace GlobalTheory.ExtAtProof

theorem injective_of_flat {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R]
    (φ : A →+* R) (hφ : φ.Flat) [IsLocalHom φ] : Function.Injective φ := by
  letI := φ.toAlgebra
  haveI : Module.Flat A R := hφ
  haveI : IsLocalHom (algebraMap A R) := ‹_›
  haveI := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := A) (B := R)
  rw [injective_iff_map_eq_zero]
  intro a ha
  have h := Ideal.comap_map_eq_self_of_faithfullyFlat (A := A) (B := R) ⊥
  rw [Ideal.map_bot] at h
  have : a ∈ Ideal.comap (algebraMap A R) ⊥ := by rw [Ideal.mem_comap, Ideal.mem_bot]; exact ha
  rw [h] at this
  simpa using this

theorem extAtSt : ExtAtSt := by
  intro X X' U Y S _ π j g sX sY R _ _ _ ξ y χ hj hsep hlft hg hflat hy hχ hχS
  haveI := hj
  haveI := hsep
  haveI := hlft
  set x' := ξ (closedPoint R) with hx'
  let A := X'.presheaf.stalk x'
  let φ : A →+* R := (Scheme.stalkClosedPointTo ξ).hom
  haveI : IsLocalHom φ := Scheme.isLocalHom_stalkClosedPointTo ξ
  have hinj : Function.Injective φ := injective_of_flat φ hflat
  haveI : IsDomain A := hinj.isDomain φ
  have hξ : ξ = spMap φ ≫ X'.fromSpecStalk x' := (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ).symm
  let γ : FractionRing A →+* FractionRing R :=
    IsLocalization.map (FractionRing R) φ (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective φ hinj)
  have hγ : ∀ a, γ (algebraMap A _ a) = algebraMap R _ (φ a) := fun a => IsLocalization.map_eq _ _
  have hsq : spMap γ ≫ jK A = jK R ≫ spMap φ := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact hγ a
  let η₀ : Sp (FractionRing A) ⟶ X' := jK A ≫ X'.fromSpecStalk x'
  have hη : spMap γ ≫ η₀ = jK R ≫ ξ := by
    rw [hξ, ← Category.assoc, hsq, Category.assoc]
  have e : spMap γ ≫ η₀ ≫ π = y ≫ j := by rw [hy, ← Category.assoc, hη, Category.assoc]
  have hr : Set.range (η₀ ≫ π) ⊆ Set.range j := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨q⟩ : Nonempty (Sp (FractionRing R)) := ⟨closedPoint _⟩
    have hp : p = spMap γ q := Subsingleton.elim (α := PrimeSpectrum (FractionRing A)) _ _
    refine ⟨y q, ?_⟩
    rw [hp, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← e]
  let u₀ : Sp (FractionRing A) ⟶ U := IsOpenImmersion.lift j (η₀ ≫ π) hr
  have hu₀ : u₀ ≫ j = η₀ ≫ π := IsOpenImmersion.lift_fac _ _ _
  have hyu : spMap γ ≫ u₀ = y := by
    rw [← cancel_mono j, Category.assoc, hu₀, e]
  obtain ⟨ψ, hψ₁, hψ₂⟩ := GlobalTheory.T.morphism_extension_from_generic_point A R φ hflat inferInstance γ hγ Y (u₀ ≫ g) χ
    (by rw [hχ, ← hyu, Category.assoc])
  have hψS : ψ ≫ sY = X'.fromSpecStalk x' ≫ π ≫ sX := by
    apply GlobalTheory.T.spec_morphism_eq_of_local_injective A R φ hinj inferInstance S
    rw [← Category.assoc, hψ₂, hχS, hξ]
    simp only [Category.assoc]
  obtain ⟨V₀, hxV₀, h₀, hh₀, hh₀S⟩ := spread_out_of_isGermInjective' (π ≫ sX) sY (x := x') ψ hψS
  obtain ⟨V, hxV, hV⟩ := GlobalTheory.FiniteBirationalNear.exists_isIntegral_nhds x'
  let V₁ : X'.Opens := V ⊓ V₀
  have hxV₁ : x' ∈ V₁ := ⟨hxV, hxV₀⟩
  refine ⟨V₁, X'.homOfLE inf_le_right ≫ h₀, hxV₁, ?_⟩
  intro T a u hau
  let O : X'.Opens := V₁ ⊓ π ⁻¹ᵁ j.opensRange
  have hOV₁ : O ≤ V₁ := inf_le_left
  have hOV : O ≤ V := hOV₁.trans inf_le_left
  let eO : O.toScheme ⟶ V₁.toScheme := X'.homOfLE hOV₁
  have hrO : Set.range (O.ι ≫ π) ⊆ Set.range j := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨u', hu'⟩ := p.2.2
    exact ⟨u', hu'⟩
  let uO : O.toScheme ⟶ U := IsOpenImmersion.lift j (O.ι ≫ π) hrO
  have huO : uO ≫ j = O.ι ≫ π := IsOpenImmersion.lift_fac _ _ _
  have hrη : Set.range η₀ ⊆ Set.range O.ι := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine ⟨?_, ?_⟩
    · have hsp : η₀ p ⤳ x' := by
        have : η₀ p ∈ Set.range (X'.fromSpecStalk x') := ⟨_, rfl⟩
        rwa [Scheme.range_fromSpecStalk] at this
      exact hsp.mem_open V₁.isOpen hxV₁
    · obtain ⟨u', hu'⟩ := hr ⟨p, rfl⟩
      exact ⟨u', hu'⟩
  let ι : Sp (FractionRing A) ⟶ O.toScheme := IsOpenImmersion.lift O.ι η₀ hrη
  have hι : ι ≫ O.ι = η₀ := IsOpenImmersion.lift_fac _ _ _
  haveI : IsDominant ι := GlobalTheory.T.isDominant_generic_stalk_open X' x' V O hxV hV hOV ι hι
  haveI : IsReduced O.toScheme := isReduced_of_isOpenImmersion (X'.homOfLE hOV)
  have hC : eO ≫ X'.homOfLE inf_le_right ≫ h₀ = uO ≫ g := by
    refine ext_of_isDominant_of_isSeparated sY ?_ ι ?_
    · simp only [eO, Category.assoc, hh₀S, Scheme.homOfLE_ι_assoc, hg, reassoc_of% huO]
    · have h3 : ι ≫ eO ≫ X'.homOfLE inf_le_right = jK A ≫ V₀.fromSpecStalkOfMem x' hxV₀ := by
        rw [← cancel_mono V₀.ι]
        simp only [eO, η₀, Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc, reassoc_of% hι, hι, Scheme.Opens.fromSpecStalkOfMem_ι]
      have h4 : ι ≫ uO = u₀ := by
        rw [← cancel_mono j, Category.assoc, huO, reassoc_of% hι, hu₀]
      rw [reassoc_of% h3, ← hh₀, hψ₁, reassoc_of% h4]
  have hrA : Set.range (a ≫ V₁.ι) ⊆ Set.range O.ι := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine ⟨?_, ?_⟩
    · rw [Scheme.Hom.comp_apply]
      exact (a t).2
    · refine ⟨u t, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← hau]
      simp
  let a' : T ⟶ O.toScheme := IsOpenImmersion.lift O.ι (a ≫ V₁.ι) hrA
  have ha' : a' ≫ O.ι = a ≫ V₁.ι := IsOpenImmersion.lift_fac _ _ _
  have h1 : a' ≫ eO = a := by rw [← cancel_mono V₁.ι, Category.assoc, Scheme.homOfLE_ι, ha']
  have h2 : a' ≫ uO = u := by rw [← cancel_mono j, Category.assoc, huO, reassoc_of% ha', hau]
  calc a ≫ X'.homOfLE inf_le_right ≫ h₀ = a' ≫ eO ≫ X'.homOfLE inf_le_right ≫ h₀ := by
        rw [← reassoc_of% h1]
    _ = u ≫ g := by rw [hC, ← Category.assoc, h2]

end GlobalTheory.ExtAtProof
