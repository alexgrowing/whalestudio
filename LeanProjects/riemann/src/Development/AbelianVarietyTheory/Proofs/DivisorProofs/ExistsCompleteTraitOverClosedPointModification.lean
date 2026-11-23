import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupNonzeroLocusEmbH
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftClosedImmersionOfDense
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsStableBasOfPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_cDvr_injective_isLocalHom (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [CharZero A] :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (ψ : A →+* W),
      GlobalTheory.LN.CDvr W ∧ Function.Injective ψ ∧ IsLocalHom ψ := by
  by_cases h : IsField A
  · letI := h.toField
    refine ⟨PowerSeries A, inferInstance, inferInstance, inferInstance, PowerSeries.C, ⟨inferInstance, ?_, ?_⟩,
      RingHom.injective _, inferInstance⟩
    · rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
    · exact charZero_of_injective_ringHom (f := PowerSeries.C (R := A)) (RingHom.injective _)
  · obtain ⟨O, _, _, _, _, φ, h1, h2⟩ := exists_complete_discreteValuationRing_dominating A h
    exact ⟨O, inferInstance, inferInstance, inferInstance, φ,
      ⟨inferInstance, inferInstance, charZero_of_injective_ringHom h1⟩, h1, h2⟩

theorem exists_trait_over_closedPoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (M : Modif R) (x₀ : M.S), M.π x₀ = closedPoint R →
      ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (ξ : Sp W ⟶ M.S),
        GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ ξ ≫ M.π = spMap φ ∧ ξ (closedPoint W) = x₀ := by
  intro R _ _ _ hB M x₀ hx
  have : IsNoetherianRing R := hB.1.1
  have : CharZero R := hB.2
  have := M.integral
  have := M.proper
  have := LocallyOfFiniteType.isLocallyNoetherian M.π
  obtain ⟨θ, hθ⟩ := Spec.map_surjective (M.S.fromSpecStalk x₀ ≫ M.π)
  have hpt : ∀ q, (Spec.map θ) q = M.π (M.S.fromSpecStalk x₀ q) := fun q => by
    rw [hθ, Scheme.Hom.comp_apply]
  have hloc : IsLocalHom θ.hom := by
    apply ((local_hom_TFAE θ.hom).out 0 4).2
    have e := hpt (closedPoint (M.S.presheaf.stalk x₀) : Spec (M.S.presheaf.stalk x₀))
    rw [Scheme.fromSpecStalk_closedPoint, hx] at e
    exact congrArg PrimeSpectrum.asIdeal e
  have hinj : Function.Injective θ.hom := by
    let pt : Sp (FractionRing R) := closedPoint (FractionRing R)
    obtain ⟨q, hq⟩ : M.gp pt ∈ Set.range (M.S.fromSpecStalk x₀) := by
      rw [Scheme.range_fromSpecStalk]
      show _ ⤳ x₀
      rw [specializes_iff_mem_closure]
      have hd := M.dominant.denseRange
      have hs : Set.range M.gp.base ⊆ {M.gp pt} := by
        rintro _ ⟨y, rfl⟩
        rw [Subsingleton.elim y (closedPoint _)]
        rfl
      exact closure_mono hs (hd.closure_range ▸ Set.mem_univ x₀)
    have h1 : (Spec.map θ) q = jK R pt := by
      rw [hpt, hq]
      exact (Scheme.Hom.comp_apply M.gp M.π pt).symm.trans (by rw [M.gp_π])
    have h2 := congrArg PrimeSpectrum.asIdeal h1
    rw [injective_iff_map_eq_zero]
    intro a ha
    have h3 : a ∈ Ideal.comap θ.hom q.asIdeal := by
      rw [Ideal.mem_comap, ha]; exact Ideal.zero_mem _
    have h4 : algebraMap R (FractionRing R) a ∈ maximalIdeal (FractionRing R) := by
      have h5 : a ∈ ((jK R) pt).asIdeal := by
        rw [← h2]; exact h3
      exact h5
    have h6 : algebraMap R (FractionRing R) a = 0 := by
      by_contra hne
      exact (maximalIdeal.isMaximal _).ne_top (Ideal.eq_top_of_isUnit_mem _ h4 (isUnit_iff_ne_zero.2 hne))
    exact IsFractionRing.injective R (FractionRing R) (h6.trans (map_zero _).symm)
  have : CharZero (M.S.presheaf.stalk x₀) := charZero_of_injective_ringHom hinj
  obtain ⟨W, _, _, _, ψ, hW, hψi, hψl⟩ := exists_cDvr_injective_isLocalHom (M.S.presheaf.stalk x₀)
  refine ⟨W, inferInstance, inferInstance, inferInstance, ψ.comp θ.hom, spMap ψ ≫ M.S.fromSpecStalk x₀, hW,
    hψi.comp hinj, RingHom.isLocalHom_comp _ _, ?_, ?_⟩
  · rw [Category.assoc, ← hθ, ← Spec.map_comp]
    rfl
  · exact (Scheme.Hom.comp_apply _ _ _).trans
      (Eq.trans (congrArg (M.S.fromSpecStalk x₀) (IsLocalRing.comap_closedPoint ψ))
        (Scheme.fromSpecStalk_closedPoint (x := x₀)))

end GlobalTheory.Mum
