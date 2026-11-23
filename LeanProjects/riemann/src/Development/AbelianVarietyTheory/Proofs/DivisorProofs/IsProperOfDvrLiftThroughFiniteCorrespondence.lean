import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperOfCompleteDVRLiftGeneric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverCompOfIsFiniteNoetherianBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.FiniteCoverProper

theorem isProper_of_lift_through_finite : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X Y₀ Y : Scheme.{0}) (τ : X ⟶ Sp R) (s t : Y ⟶ X) (i : Y₀ ⟶ Y), IsQProjOver τ → IsFinite s → IsOpenImmersion i → IsDominant i → t ≫ τ = s ≫ τ → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ i ≫ t → ∃ z : Sp V ⟶ X, spMap (algebraMap V K) ≫ z = x ≫ i ≫ s) → IsProper t := by
  intro R _ _ X Y₀ Y τ s t i hτ hs hi hd ht h
  have hX : IsLocallyNoetherian X := by
    obtain ⟨N, j, hj, -, e⟩ := hτ
    have : IsProper (PSpace.str R N) := isProper_str R N
    have : LocallyOfFiniteType τ := by rw [← e]; infer_instance
    have : IsLocallyNoetherian (Sp R) :=
      inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of R)))
    exact LocallyOfFiniteType.isLocallyNoetherian τ
  have hsep : IsSeparated τ := by
    obtain ⟨N, j, hj, -, e⟩ := hτ
    have : IsProper (PSpace.str R N) := isProper_str R N
    have : IsImmersion j := hj
    rw [← e]; infer_instance
  have hY : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have hq : IsQProjOver (t ≫ τ) := ht ▸ GlobalTheory.isQProjOver_comp_of_isFinite_general s hτ
  refine GlobalTheory.ValuativeGeneric.isProper_of_lift_generic R Y X t τ hsep hq ?_
  intro V K _ _ _ _ _ _ _ x y hx hxy
  have hgen : genericPoints Y ⊆ Set.range i := GlobalTheory.genericPoints_subset_range_of_isDominant i
  have hr : Set.range x ⊆ Set.range i := hx.trans hgen
  have hx₀ : IsOpenImmersion.lift i x hr ≫ i = x := IsOpenImmersion.lift_fac i x hr
  obtain ⟨z, hz⟩ := h V K y (IsOpenImmersion.lift i x hr) (by rw [← Category.assoc, hx₀, hxy])
  have hE : ValuativeCriterion.Existence s :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed s) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) s).1
  have hw : x ≫ s = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ z := by
    rw [← hx₀, Category.assoc]; exact hz.symm
  obtain ⟨⟨x', hx', -⟩⟩ := (hE { R := V, K := K, i₁ := x, i₂ := z, commSq := ⟨hw⟩ }).exists_lift
  exact ⟨x', hx'⟩

end GlobalTheory.FiniteCoverProper
