import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompHt GlobalTheory.AllWt

set_option autoImplicit false

namespace GlobalTheory.FinDesc

theorem spField_pt_eq (K : Type) [Field K] (a b : Sp K) : a = b := by
  have h : ∀ c : PrimeSpectrum K, c.asIdeal = ⊥ := fun c => Ideal.eq_bot_of_prime c.asIdeal
  exact PrimeSpectrum.ext ((h a).trans (h b).symm)

theorem exists_finite_subext_point : ∀ (X S : Scheme.{0}) (s : X ⟶ S), LocallyOfFiniteType s → ∀ (K₀ K : Type) [Field K₀]
    [Field K] [Algebra K₀ K], Algebra.IsAlgebraic K₀ K → ∀ (y : Sp K ⟶ X) (z : Sp K₀ ⟶ S),
    y ≫ s = spMap (algebraMap K₀ K) ≫ z → ∃ (L : IntermediateField K₀ K) (yL : Sp L ⟶ X), FiniteDimensional K₀ L ∧
      spMap (algebraMap L K) ≫ yL = y ∧ yL ≫ s = spMap (algebraMap K₀ L) ≫ z := by
  intro X S s hs K₀ K _ _ _ halg y z hyz
  classical
  let pb : Sp K := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  have hpt : ∀ a : Sp K₀, z a = s (y pb) := fun a => by
    have e := congrArg (fun h : Sp K ⟶ S => h pb) hyz
    simp only [Scheme.Hom.comp_apply] at e
    rw [e, spField_pt_eq K₀ a]
  obtain ⟨U, hU, hqU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens)
    (show s (y pb) ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨V, hV, hgV, hVU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
    (show y pb ∈ s ⁻¹ᵁ U from hqU)
  have hU' : IsAffineOpen U := hU
  have hV' : IsAffineOpen V := hV
  have hry : Set.range y ⊆ Set.range hV'.fromSpec := by
    rw [hV'.range_fromSpec]
    rintro _ ⟨a, rfl⟩
    rw [spField_pt_eq K a pb]
    exact hgV
  have hrz : Set.range z ⊆ Set.range hU'.fromSpec := by
    rw [hU'.range_fromSpec]
    rintro _ ⟨a, rfl⟩
    rw [hpt a]
    exact hqU
  have hy₁ := IsOpenImmersion.lift_fac hV'.fromSpec y hry
  have hz₁ := IsOpenImmersion.lift_fac hU'.fromSpec z hrz
  rw [← Spec.map_preimage (IsOpenImmersion.lift hV'.fromSpec y hry)] at hy₁
  rw [← Spec.map_preimage (IsOpenImmersion.lift hU'.fromSpec z hrz)] at hz₁
  set φ := Spec.preimage (IsOpenImmersion.lift hV'.fromSpec y hry) with hφ
  set ψ := Spec.preimage (IsOpenImmersion.lift hU'.fromSpec z hrz) with hψ
  have key : s.appLE U V hVU ≫ φ = ψ ≫ CommRingCat.ofHom (algebraMap K₀ K) := by
    apply Spec.map_injective
    rw [← cancel_mono hU'.fromSpec, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      IsAffineOpen.SpecMap_appLE_fromSpec s hU' hV' hVU, ← Category.assoc, hy₁, hz₁]
    exact hyz
  have hft := LocallyOfFiniteType.finiteType_appLE s hU' hV' hVU
  let _ := (s.appLE U V hVU).hom.toAlgebra
  obtain ⟨T, hT⟩ := hft.out
  let L : IntermediateField K₀ K := IntermediateField.adjoin K₀ ((T.image φ.hom : Finset K) : Set K)
  have hfin : FiniteDimensional K₀ L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (halg.isAlgebraic x).isIntegral
  have hmem : ∀ b : Γ(X, V), φ.hom b ∈ L := by
    intro b
    have hb : b ∈ Algebra.adjoin Γ(S, U) (T : Set Γ(X, V)) := by rw [hT]; exact Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem b hb => exact IntermediateField.subset_adjoin _ _ (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hb))
    | algebraMap a =>
      have e := congrArg (fun h => h.hom a) key
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
      rw [RingHom.algebraMap_toAlgebra, e]
      exact L.algebraMap_mem _
    | add b c _ _ hb hc => rw [map_add]; exact L.add_mem hb hc
    | mul b c _ _ hb hc => rw [map_mul]; exact L.mul_mem hb hc
  let φL : Γ(X, V) →+* L := φ.hom.codRestrict L hmem
  refine ⟨L, Spec.map (CommRingCat.ofHom φL : Γ(X, V) ⟶ CommRingCat.of L) ≫ hV'.fromSpec, hfin, ?_, ?_⟩
  · rw [← hy₁, ← Category.assoc]
    congr 1
    rw [spMap, ← Spec.map_comp]
    congr 1
  · have key' : s.appLE U V hVU ≫ CommRingCat.ofHom φL = ψ ≫ CommRingCat.ofHom (algebraMap K₀ L) := by
      ext a
      have e := congrArg (fun h => h.hom a) key
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e ⊢
      exact e
    rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec s hU' hV' hVU, ← Category.assoc, ← Spec.map_comp, key',
      Spec.map_comp, ← hz₁, spMap]
    simp only [Category.assoc]

end GlobalTheory.FinDesc
