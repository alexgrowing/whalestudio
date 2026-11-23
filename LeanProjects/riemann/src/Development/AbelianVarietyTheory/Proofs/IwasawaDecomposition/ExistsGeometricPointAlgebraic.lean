import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_algebraic_point_of_fiber : ∀ {A : Type} [CommRing A] {B : Scheme.{0}} (f : Sp A ⟶ B)
    [LocallyOfFiniteType f] (x : Sp A) (K' : Type) [Field K']
    [IsAlgClosed K'] (ι : B.residueField (f x) →+* K'),
    ∃ ψ₁ : A →+* K', spMap ψ₁ ≫ f = spMap ι ≫ B.fromSpecResidueField (f x) ∧
      ∀ r, @IsAlgebraic (B.residueField (f x)) K' _ _ ι.toAlgebra (ψ₁ r) := by
  intro A _ B f _ x K' _ _ ι
  let s : f.fiber (f x) ⟶ Spec (B.residueField (f x)) := f.fiberToSpecResidueField (f x)
  haveI : LocallyOfFiniteType s := by
    show LocallyOfFiniteType (pullback.snd _ _)
    infer_instance
  haveI : JacobsonSpace (f.fiber (f x)) := LocallyOfFiniteType.jacobsonSpace s
  have hx : x ∈ Set.range (f.fiberι (f x)) := by
    rw [f.range_fiberι]; rfl
  obtain ⟨x', -⟩ := hx
  obtain ⟨z, -, hz⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set (f.fiber (f x))))
    ⟨x', trivial⟩ isClosed_univ.isLocallyClosed
  have h1 : LocallyOfFiniteType ((f.fiber (f x)).fromSpecResidueField z) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hz
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((f.fiber (f x)).fromSpecResidueField z ≫ s)
  have hft : φ.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map φ) := hφ ▸ inferInstance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp this
  letI : Algebra (B.residueField (f x)) ((f.fiber (f x)).residueField z) := φ.hom.toAlgebra
  haveI : Algebra.FiniteType (B.residueField (f x)) ((f.fiber (f x)).residueField z) := hft
  haveI : Module.Finite (B.residueField (f x)) ((f.fiber (f x)).residueField z) :=
    finite_of_finite_type_of_isJacobsonRing _ _
  haveI : Algebra.IsAlgebraic (B.residueField (f x)) ((f.fiber (f x)).residueField z) :=
    Algebra.IsAlgebraic.of_finite _ _
  letI : Algebra (B.residueField (f x)) K' := ι.toAlgebra
  let j : (f.fiber (f x)).residueField z →ₐ[B.residueField (f x)] K' := IsAlgClosed.lift
  obtain ⟨θ, hθ⟩ := Spec.map_surjective ((f.fiber (f x)).fromSpecResidueField z ≫ f.fiberι (f x))
  have hjφ : φ ≫ CommRingCat.ofHom (j : (f.fiber (f x)).residueField z →+* K') = CommRingCat.ofHom ι := by
    ext c
    exact j.commutes c
  refine ⟨(j : (f.fiber (f x)).residueField z →+* K').comp θ.hom, ?_, fun r => ?_⟩
  · have e1 : spMap ((j : (f.fiber (f x)).residueField z →+* K').comp θ.hom) =
        Spec.map (CommRingCat.ofHom (j : (f.fiber (f x)).residueField z →+* K')) ≫ Spec.map θ := by
      rw [← Spec.map_comp]; rfl
    have e2 : f.fiberι (f x) ≫ f = s ≫ B.fromSpecResidueField (f x) := pullback.condition
    rw [e1, hθ, Category.assoc, Category.assoc, e2, ← Category.assoc ((f.fiber (f x)).fromSpecResidueField z),
      ← hφ, ← Category.assoc, ← Spec.map_comp]
    exact congrArg (fun g => Spec.map g ≫ B.fromSpecResidueField (f x)) hjφ
  · exact (Algebra.IsAlgebraic.isAlgebraic (θ.hom r)).algHom j

end GlobalTheory
