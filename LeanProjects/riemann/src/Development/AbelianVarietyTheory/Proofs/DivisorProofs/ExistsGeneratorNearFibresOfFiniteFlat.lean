import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorOnSmallerOpenOfNonvanishingSectioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdsNonzeroOfIsClosedMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecializationClosedInAffineNeighbourhoodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatLocalBaseChangeOfProperPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingOverClosedPointFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroSectionOfFiniteFreeBaseChangeStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_gen_near_of_finFlat : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ρ.Flat → ∀ (Z Y Z' Y' : Scheme.{0}) (p : Z ⟶ Y) (p' : Z' ⟶ Y') (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (k : Y' ⟶ Y) (k' : Z' ⟶ Z), IsPullback k y' y (spMap ρ) → IsPullback k' p' p k → IsProper p → IsLocallyNoetherian Y → (∀ V : Y.Opens, Function.Bijective (p.app V).hom) → ∀ L' : LB Z, L'.IsLB → (∀ x : Y', ∃ V : Y'.Opens, x ∈ V ∧ ∃ t : LB.Gen ((L'.pull k').pull (p' ⁻¹ᵁ V).ι), t.IsGen) → ∀ x : Y, ∃ V : Y.Opens, x ∈ V ∧ ∃ t : LB.Gen (L'.pull (p ⁻¹ᵁ V).ι), t.IsGen := by
  intro R _ _ _ hR R' _ _ _ ρ hfin hflat Z Y Z' Y' p p' y y' k k' hk hk' hp hY hbij L hL hloc x
  haveI : IsNoetherianRing R := hR.1
  obtain ⟨hkf, hqc, hqs, hsurj, hcl, hclp, hO, d, b, hb⟩ :=
    GlobalTheory.T.finite_flat_local_baseChange_of_proper_properties R R' ρ hfin.2.1 hfin.2.2 hflat Z Y Z' Y' p p' y y' k k' hk hk' hp
  obtain ⟨V, hV, y₀, hy₀, hxy, hE⟩ := GlobalTheory.T.exists_specialization_closed_in_affine_neighbourhood Y x
  obtain ⟨hclV, -⟩ := hE V le_rfl hV hy₀
  have hL' : (L.pull k').IsLB := LB.isLB_pull hL _
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_section_nonvanishing_over_closed_point_fibre Y Y' Z' k hkf p' hqc hqs V hV y₀ hy₀ hclV (L.pull k') hL' (fun x' _ => hloc x')
  obtain ⟨V₁, hy₁, hV₁V, hV₁⟩ := GlobalTheory.T.exists_nhds_subset_nonzeroLocus_of_isClosedMap Z' Y (p' ≫ k) hcl (L.pull k') V s y₀ hy₀ hs
  obtain ⟨f, hf1, hf2⟩ := hV.exists_basicOpen_le ⟨y₀, hy₁⟩ hy₀
  have hV₂V : Y.basicOpen f ≤ V := Y.basicOpen_le f
  have hV₂ : IsAffineOpen (Y.basicOpen f) := hV.basicOpen f
  obtain ⟨-, M, hM, hMiff⟩ := hE (Y.basicOpen f) hV₂V hV₂ hf2
  have hcomm : ∀ z : Z', p (k' z) = k (p' z) := fun z => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hk'.w]
  have hle : k' ⁻¹ᵁ (p ⁻¹ᵁ Y.basicOpen f) ≤ p' ⁻¹ᵁ (k ⁻¹ᵁ V) := fun z hz => by
    show k (p' z) ∈ V
    rw [← hcomm]
    exact hV₂V hz
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_generator_on_smaller_open_of_nonvanishing_section Z' (L.pull k') hL' _ _ hle s (fun z₀ hz₀ => hV₁ z₀ (by
    rw [Scheme.Hom.comp_apply, ← hcomm]
    exact hf1 hz₀))
  have hsurjp : Function.Surjective (p.app (Y.basicOpen f)).hom := (hbij _).2
  let e := RingEquiv.ofBijective (p.app (Y.basicOpen f)).hom (hbij _)
  haveI hm : (Ideal.comap e.symm.toRingHom M).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ e.symm.surjective
  obtain ⟨hOc, hOq⟩ := hO _ hV₂
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_nonzero_section_of_finite_free_baseChange R R' ρ d b hb Z Z' k' (p ≫ y) (p' ≫ y') (hk'.paste_vert hk) (p ⁻¹ᵁ Y.basicOpen f) hOc hOq
    L hL σ hσ _ hm
  have hfib : ∀ z₀ : (p ⁻¹ᵁ Y.basicOpen f).toScheme, p ((p ⁻¹ᵁ Y.basicOpen f).ι z₀) = y₀ → z₀ ∈ nonzeroLocus u := by
    intro z₀ hz₀
    obtain ⟨z', hz'⟩ := hsurj ((p ⁻¹ᵁ Y.basicOpen f).ι z₀)
    have hz'O : z' ∈ k' ⁻¹ᵁ (p ⁻¹ᵁ Y.basicOpen f) := by
      show k' z' ∈ p ⁻¹ᵁ Y.basicOpen f
      rw [hz']
      first | exact z₀.2 | simpa using z₀.2 | exact (Scheme.Opens.range_ι _).subset ⟨z₀, rfl⟩
    obtain ⟨w, hw⟩ : z' ∈ Set.range (k' ⁻¹ᵁ (p ⁻¹ᵁ Y.basicOpen f)).ι.base := by
      rw [Scheme.Opens.range_ι]; exact hz'O
    refine hu w (fun a ha => ?_) z₀ (by rw [← hz']; exact congrArg k'.base hw |>.symm)
    have ha₀ : e.symm a ∈ M := ha
    have ea : a = p.app (Y.basicOpen f) (e.symm a) := (e.apply_symm_apply a).symm
    intro hmem
    rw [ea, ← Scheme.preimage_basicOpen] at hmem
    have : k' ((k' ⁻¹ᵁ (p ⁻¹ᵁ Y.basicOpen f)).ι w) = (p ⁻¹ᵁ Y.basicOpen f).ι z₀ := by
      rw [← hz']; exact congrArg k'.base hw
    rw [this] at hmem
    have hmem' : p ((p ⁻¹ᵁ Y.basicOpen f).ι z₀) ∈ Y.basicOpen (e.symm a) := hmem
    rw [hz₀] at hmem'
    exact (hMiff _).1 ha₀ hmem'
  obtain ⟨V₃, hy₃, hV₃, hV₃u⟩ := GlobalTheory.T.exists_nhds_subset_nonzeroLocus_of_isClosedMap Z Y p hclp L _ u y₀ hf2 hfib
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_generator_on_smaller_open_of_nonvanishing_section Z L hL (p ⁻¹ᵁ V₃) (p ⁻¹ᵁ Y.basicOpen f) (fun z hz => hV₃ hz) u
    (fun z hz => hV₃u z hz)
  exact ⟨V₃, hxy.mem_open V₃.isOpen hy₃, t, ht⟩

end GlobalTheory.Mum
