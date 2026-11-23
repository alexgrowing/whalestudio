import Mathlib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev Sp (R : Type) [CommRing R] : Scheme.{0} := Spec (CommRingCat.of R)

abbrev spMap {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') : Sp R' ⟶ Sp R :=
  Spec.map (CommRingCat.ofHom f)

abbrev PSpace (R : Type) [CommRing R] (N : ℕ) : Scheme.{0} :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)

def PSpace.str (R : Type) [CommRing R] (N : ℕ) : PSpace R N ⟶ Sp R :=
  Proj.toSpecZero _ ≫ spMap (algebraMap R ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0))

def IsProjOver {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) : Prop :=
  ∃ (N : ℕ) (i : X ⟶ PSpace R N), IsClosedImmersion i ∧ i ≫ PSpace.str R N = f

def IsQProjOver {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) : Prop :=
  ∃ (N : ℕ) (i : X ⟶ PSpace R N), IsImmersion i ∧ QuasiCompact i ∧ i ≫ PSpace.str R N = f

def IsNormalScheme (X : Scheme.{0}) : Prop :=
  ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)

structure IsCompletedStrictHens (A R : Type) [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R]
    [Algebra A R] [IsLocalHom (algebraMap A R)] : Prop where
  noeth : IsNoetherianRing R
  complete : IsAdicComplete (IsLocalRing.maximalIdeal R) R
  flat : Module.Flat A R
  unram : (IsLocalRing.maximalIdeal A).map (algebraMap A R) = IsLocalRing.maximalIdeal R
  res : IsSepClosure (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField R)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
