import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Models GlobalTheory.UPoinc GlobalTheory.ZH

namespace GlobalTheory.UPoinc

theorem isReduced_of_flat_isPreimmersion {X Y : Scheme.{0}} (f : X ⟶ Y) [Flat f] [IsPreimmersion f] [IsReduced Y] :
    IsReduced X := by
  haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have hfl := Flat.stalkMap f x
    have hs := f.stalkMap_surjective x
    letI := (f.stalkMap x).hom.toAlgebra
    haveI : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := hfl
    haveI : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
    haveI := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (f x)) (B := X.presheaf.stalk x)
    have hi : Function.Injective (f.stalkMap x).hom :=
      FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
    exact isReduced_of_injective (RingEquiv.ofBijective _ ⟨hi, hs⟩).symm (RingEquiv.injective _)
  exact isReduced_of_isReduced_stalk X

theorem isIntegral_pullback_toRat : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [CharZero Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens) (R : Subalgebra o Ω) (u₀ : U₀.toScheme ⟶ Sp R), (U₀ : Set M.Z).Nonempty → (∀ x : Sp Ω ⟶ U₀.toScheme, x ≫ U₀.ι = M.pt → x ≫ u₀ = spMap R.val.toRingHom) → IsIntegral (pullback u₀ (spMap (toRat R))) ∧ ∃ pt : Sp Ω ⟶ pullback u₀ (spMap (toRat R)), pt ≫ pullback.fst _ _ ≫ U₀.ι = M.pt ∧ Dense (Set.range pt) := by
  intro o Ω _ _ _ _ M U₀ R u₀ hne hgen
  haveI := M.integral
  letI := (toRat R).toAlgebra
  haveI := isLocalization_ratHull R
  haveI : IsPreimmersion (spMap (toRat R)) :=
    IsPreimmersion.of_isLocalization (Algebra.algebraMapSubmonoid R (nonZeroDivisors ℤ))
  haveI : Flat (spMap (toRat R)) := (HasRingHomProperty.Spec_iff (P := @Flat)).2
    (IsLocalization.flat (ratHull R) (Algebra.algebraMapSubmonoid R (nonZeroDivisors ℤ)))
  have hr : Set.range M.pt ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hne (show w ∈ (⊤ : (Sp Ω).Opens) from trivial)
  have hx := IsOpenImmersion.lift_fac U₀.ι M.pt hr
  have w : IsOpenImmersion.lift U₀.ι M.pt hr ≫ u₀ = spMap (ratHull R).val.toRingHom ≫ spMap (toRat R) :=
    (hgen _ hx).trans (spMap_val_toRat R).symm
  let pt := pullback.lift _ _ w
  let j : pullback u₀ (spMap (toRat R)) ⟶ M.Z := pullback.fst _ _ ≫ U₀.ι
  have hpt : pt ≫ j = M.pt := by rw [← Category.assoc, pullback.lift_fst, hx]
  haveI : IsPreimmersion j := inferInstance
  haveI : Flat j := inferInstance
  haveI := isReduced_of_flat_isPreimmersion j
  have hj : ∀ y, j (pt y) = genericPoint M.Z := fun y => by
    rw [← Scheme.Hom.comp_apply, hpt]
    exact M.gen.le ⟨y, rfl⟩
  have hg : IsGenericPoint (pt default) Set.univ := by
    refine isGenericPoint_iff_specializes.2 fun z => ⟨fun _ => trivial, fun _ => ?_⟩
    rw [← j.isEmbedding.isInducing.specializes_iff, hj]
    exact genericPoint_specializes _
  haveI : IrreducibleSpace (pullback u₀ (spMap (toRat R)) :) :=
    (irreducibleSpace_def _).2 hg.isIrreducible
  refine ⟨isIntegral_of_irreducibleSpace_of_isReduced _, pt, hpt, ?_⟩
  exact Dense.mono (Set.singleton_subset_iff.2 ⟨default, rfl⟩) (dense_iff_closure_eq.2 hg)

end GlobalTheory.UPoinc
