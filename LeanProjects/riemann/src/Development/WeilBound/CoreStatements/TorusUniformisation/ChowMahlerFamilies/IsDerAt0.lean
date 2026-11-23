import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FromNAdd
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT
open scoped Matrix

noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

abbrev Ix (E : Type) [Field E] [NumberField E] (n : ℕ) : Type := Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 E)

def dl {E : Type} [Field E] [NumberField E] {n : ℕ} (m : Ix E n) : Fin n → 𝓞 E :=
  Pi.single m.1 (RingOfIntegers.basis E m.2)

def mkN {E : Type} [Field E] [NumberField E] {n : ℕ} (p : ℕ) (x : Fin n → 𝓞 E) : TestPt.NAdd E n p :=
  fun i => Ideal.Quotient.mk _ (x i)

def toRC {O Ω C : Type} [CommRing O] [Field Ω] [Field C] [Algebra O Ω] [Algebra O C] [Algebra Ω C]
    (R : Subalgebra O Ω) (RC : Subalgebra O C) (h : ∀ a ∈ R, algebraMap Ω C a ∈ RC) : R →+* RC :=
  ((algebraMap Ω C).comp (R.val : R →+* Ω)).codRestrict RC fun a => h a a.2

theorem coe_toRC {O Ω C : Type} [CommRing O] [Field Ω] [Field C] [Algebra O Ω] [Algebra O C] [Algebra Ω C]
    (R : Subalgebra O Ω) (RC : Subalgebra O C) (h : ∀ a ∈ R, algebraMap Ω C a ∈ RC) (a : R) :
    ((toRC R RC h a : RC) : C) = algebraMap Ω C a := rfl

def IsDerAt0 {C R W N : Type} [Field C] [CommRing R] [Algebra R C] [AddCommGroup W] [Module R W] [AddCommGroup N]
    (M : Submodule R (N → C)) (Dv : M →ₗ[R] W) : Prop :=
  ∀ (f g h : M) (a b : R), (h : N → C) = (f : N → C) * (g : N → C) → algebraMap R C a = (f : N → C) 0 →
    algebraMap R C b = (g : N → C) 0 → Dv h = a • Dv g + b • Dv f

end PositivityTheory.Xgn.TestGroupPoint
