import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringLiftOfSpecialFibre
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField

open CategoryTheory AlgebraicGeometry Topology

namespace GlobalTheory.CurveThrough

theorem exists_curve_through_closedPoint :
    ∀ (κ : Type) [Field κ] (V : Scheme.{0}) [IsIntegral V] (q : V ⟶ Spec (CommRingCat.of κ))
    [LocallyOfFiniteType q] (x : V) (U : V.Opens), IsClosed ({x} : Set V) → (∃ v, v ∈ U) →
    x ∉ U → ∃ y : V, y ∈ U ∧ y ⤳ x ∧ topologicalKrullDim (closure ({y} : Set V)) = 1 := by
  intro κ _ V _ q _ x U hx hU hxU
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    V.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  replace hW : IsAffineOpen W := hW
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  let φ := Spec.preimage (hW.fromSpec ≫ q)
  have hφ : Spec.map φ = hW.fromSpec ≫ q := Spec.map_preimage _
  letI : Algebra κ Γ(V, W) := φ.hom.toAlgebra
  haveI hft : Algebra.FiniteType κ Γ(V, W) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
  haveI : IsNoetherianRing Γ(V, W) := Algebra.FiniteType.isNoetherianRing κ _
  obtain ⟨f, hemb, hfr⟩ : ∃ f : PrimeSpectrum Γ(V, W) → V, IsOpenEmbedding f ∧ Set.range f = W :=
    ⟨hW.fromSpec, hW.fromSpec.isOpenEmbedding, hW.range_fromSpec⟩
  obtain ⟨pt, hpt⟩ : ∃ pt : PrimeSpectrum Γ(V, W), f pt = x := by
    rw [← Set.mem_range, hfr]; exact hxW
  have hmax : pt.asIdeal.IsMaximal := by
    rw [← PrimeSpectrum.isClosed_singleton_iff_isMaximal]
    have e : ({pt} : Set (PrimeSpectrum Γ(V, W))) = f ⁻¹' {x} := by
      ext z
      simp only [Set.mem_singleton_iff, Set.mem_preimage, ← hpt]
      exact hemb.injective.eq_iff.symm
    rw [e]
    exact hx.preimage hemb.continuous
  have hgen := genericPoint_spec V
  have hηU : genericPoint V ∈ U := (hgen.mem_open_set_iff U.isOpen).mpr
    (by obtain ⟨v, hv⟩ := hU; exact ⟨v, trivial, hv⟩)
  have hηW : genericPoint V ∈ W := (hgen.mem_open_set_iff W.isOpen).mpr ⟨x, trivial, hxW⟩
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : PrimeSpectrum Γ(V, W), f p₀ = genericPoint V := by
    rw [← Set.mem_range, hfr]; exact hηW
  have hp₀le : p₀.asIdeal ≤ pt.asIdeal := by
    show p₀ ≤ pt
    rw [PrimeSpectrum.le_iff_specializes, ← hemb.isInducing.specializes_iff, hp₀, hpt]
    exact hgen.specializes (Set.mem_univ x)
  obtain ⟨q', hq'U, hqm, h1⟩ := GlobalTheory.exists_mem_height_map_le_one pt.asIdeal
    (U := f ⁻¹' (U : Set V)) (U.isOpen.preimage hemb.continuous)
    ⟨p₀, by rw [Set.mem_preimage, hp₀]; exact hηU, hp₀le⟩
  have hsurj := Ideal.Quotient.mk_surjective (I := q'.asIdeal)
  have hmax' : (pt.asIdeal.map (Ideal.Quotient.mk q'.asIdeal)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le hsurj (by simpa using hqm)
  have h2 : (pt.asIdeal.map (Ideal.Quotient.mk q'.asIdeal)).height ≠ 0 := by
    rw [Ne, Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot,
      Set.mem_singleton_iff]
    intro e
    have hle : pt.asIdeal ≤ q'.asIdeal := fun a ha => by
      have := Ideal.mem_map_of_mem (Ideal.Quotient.mk q'.asIdeal) ha
      rwa [e, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    have hq : q' = pt := PrimeSpectrum.ext (le_antisymm hqm hle)
    apply hxU
    rw [← hpt, ← hq]
    exact hq'U
  have h3 := le_antisymm h1 (Order.one_le_iff_ne_zero.2 h2)
  obtain ⟨s, hs1, hs2⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := κ) (A := Γ(V, W) ⧸ q'.asIdeal)
  have h4 := ReciprocityTheory.CA.height_eq_of_isMaximal_of_trdeg_eq_field s hs2
    (pt.asIdeal.map (Ideal.Quotient.mk q'.asIdeal))
  rw [h3] at h4
  have h5 : s = 1 := by exact_mod_cast h4.symm
  have hdim : ringKrullDim (Γ(V, W) ⧸ q'.asIdeal) = 1 := by rw [hs1, h5]; rfl
  refine ⟨f q', hq'U, ?_, ?_⟩
  · rw [← hpt]
    exact ((PrimeSpectrum.le_iff_specializes _ _).mp hqm).map hemb.continuous
  set y := f q' with hy
  obtain ⟨Z, i, hi, hZ, hgenZ⟩ := GlobalTheory.exists_isClosedImmersion_genericPoint y
  have hrange : Set.range i = closure ({y} : Set V) := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq, hgenZ] at h₁
    exact (isGenericPoint_def.mp h₁).symm
  have hyW : y ∈ W := by
    show y ∈ (W : Set V)
    rw [← hfr]; exact ⟨q', rfl⟩
  have hηZ : genericPoint Z ∈ (i ⁻¹ᵁ W : Z.Opens) := by
    show i (genericPoint Z) ∈ W
    rw [hgenZ]; exact hyW
  have d1 : topologicalKrullDim (closure ({y} : Set V)) = topologicalKrullDim Z :=
    GlobalTheory.topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hrange
  have d2 : topologicalKrullDim ((i ⁻¹ᵁ W : Z.Opens) : Set Z) = topologicalKrullDim Z :=
    GlobalTheory.OpenDim.topologicalKrullDim_open κ (i ≫ q) (i ⁻¹ᵁ W) ⟨_, hηZ⟩
  have d3 : topologicalKrullDim (closure ({y} : Set V) ∩ W : Set V) =
      topologicalKrullDim ((i ⁻¹ᵁ W : Z.Opens) : Set Z) := by
    refine GlobalTheory.topologicalKrullDim_eq_of_isEmbedding
      (i.isClosedEmbedding.isEmbedding.comp IsEmbedding.subtypeVal) ?_
    rw [Set.range_comp, Subtype.range_coe, ← hrange]
    ext v; constructor
    · rintro ⟨z, hz, rfl⟩; exact ⟨⟨z, rfl⟩, hz⟩
    · rintro ⟨⟨z, rfl⟩, hz⟩; exact ⟨z, hz, rfl⟩
  have d4 : topologicalKrullDim (closure ({y} : Set V) ∩ W : Set V) =
      topologicalKrullDim (PrimeSpectrum (Γ(V, W) ⧸ q'.asIdeal)) := by
    refine GlobalTheory.topologicalKrullDim_eq_of_isEmbedding
      (hemb.isEmbedding.comp (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _
        (Ideal.Quotient.mk q'.asIdeal) hsurj).isEmbedding) ?_
    rw [Set.range_comp, range_comap_of_surjective (f := Ideal.Quotient.mk q'.asIdeal) (hf := hsurj), Ideal.mk_ker]
    ext v; constructor
    · rintro ⟨p, hp, rfl⟩
      have hle : q' ≤ p := (PrimeSpectrum.mem_zeroLocus _ _).mp hp
      refine ⟨specializes_iff_mem_closure.mp
        (((PrimeSpectrum.le_iff_specializes q' p).mp hle).map hemb.continuous), ?_⟩
      rw [← hfr]; exact ⟨p, rfl⟩
    · rintro ⟨hv, hvW⟩
      rw [← hfr] at hvW
      obtain ⟨p, rfl⟩ := hvW
      refine ⟨p, ?_, rfl⟩
      have h := hemb.isInducing.specializes_iff.mp (specializes_iff_mem_closure.mpr hv)
      exact (PrimeSpectrum.mem_zeroLocus _ _).mpr ((PrimeSpectrum.le_iff_specializes _ _).mpr h)
  rw [d1, ← d2, ← d3, d4, PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, hdim]

end GlobalTheory.CurveThrough
