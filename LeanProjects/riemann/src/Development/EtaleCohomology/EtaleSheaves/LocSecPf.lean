import Development.EtaleCohomology.EtaleSheaves.LeafLocPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LocSecPf

abbrev pt (R : Type) [CommRing R] (X : Scheme.{0}) : Cx R :=
  (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj ((free R).obj (yoneda.obj X))

def LocSecA : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (F : Shv R) (n : ℤ),
  Nonempty (H R (sch.obj X) F n ≃+ CohomologyClass (pt R X) (res R F) n)

def LocSecB : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (F : Shv R) (n : ℤ),
  Nonempty (CohomologyClass (pt R X) (res R F) n ≃+ (LateralTheory.E.LeafLocPf.secCx F X).homology n)

theorem LocSec_of (hA : LocSecA) (hB : LocSecB) : LateralTheory.E.LeafLocPf.LocSec := by
  intro _ R _ X F n
  obtain ⟨a⟩ := hA R X F n
  obtain ⟨b⟩ := hB R X F n
  exact ⟨a.trans b⟩

end LateralTheory.E.LocSecPf
