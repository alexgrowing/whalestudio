import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem exists_finite_ext_point_lift_of_surjective_lft :
    ∀ {X Y : Scheme.{0}} (π : Y ⟶ X), LocallyOfFiniteType π → Function.Surjective π →
      ∀ (K : Type) [Field K] (x : Sp K ⟶ X),
        ∃ (K' : Type) (_ : Field K') (σ : K →+* K') (y : Sp K' ⟶ Y),
          σ.Finite ∧ y ≫ π = spMap σ ≫ x := by
  intro X Y π hft hs K _ x
  haveI : Surjective π := ⟨hs⟩
  let P := Limits.pullback π x
  let s : P ⟶ Sp K := Limits.pullback.snd π x
  haveI : LocallyOfFiniteType s := inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd π x))
  haveI : Surjective s := inferInstanceAs (Surjective (Limits.pullback.snd π x))
  haveI : JacobsonSpace P := LocallyOfFiniteType.jacobsonSpace s
  obtain ⟨p₀, -⟩ := s.surjective (default : Sp K)
  obtain ⟨z, -, hz⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set P)) ⟨p₀, trivial⟩
    isClosed_univ.isLocallyClosed
  haveI : IsClosedImmersion (P.fromSpecResidueField z) :=
    isClosed_singleton_iff_isClosedImmersion.mp hz
  haveI : IsFinite (P.fromSpecResidueField z ≫ s) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.2 inferInstance
  let φ := Spec.preimage (P.fromSpecResidueField z ≫ s)
  have hφ : Spec.map φ = P.fromSpecResidueField z ≫ s := Spec.map_preimage _
  refine ⟨P.residueField z, inferInstance, φ.hom,
    P.fromSpecResidueField z ≫ Limits.pullback.fst π x, ?_, ?_⟩
  · rw [← IsFinite.SpecMap_iff, hφ]; infer_instance
  · have h2 : spMap φ.hom = P.fromSpecResidueField z ≫ s := hφ
    rw [h2]
    exact (Category.assoc _ _ _).trans ((congrArg (P.fromSpecResidueField z ≫ ·)
      Limits.pullback.condition).trans (Category.assoc _ _ _).symm)

end GlobalTheory
