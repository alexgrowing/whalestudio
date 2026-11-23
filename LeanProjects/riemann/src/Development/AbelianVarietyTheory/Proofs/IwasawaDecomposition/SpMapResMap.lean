import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FlagGen

def resMap {A : Type} [CommRing A] (x : Sp A) : A →+* (Sp A).residueField x :=
  (Spec.preimage ((Sp A).fromSpecResidueField x)).hom

theorem spMap_resMap {A : Type} [CommRing A] (x : Sp A) : spMap (resMap x) = (Sp A).fromSpecResidueField x :=
  Spec.map_preimage _

abbrev Low (m : ℕ) : Type := {q : Fin m × Fin m // q.1 < q.2}

def uni {R : Type} [CommRing R] {m : ℕ} (s : Low m → R) (j i : Fin m) : R :=
  if h : i < j then s ⟨(i, j), h⟩ else if j = i then 1 else 0

end GlobalTheory.FlagGen
