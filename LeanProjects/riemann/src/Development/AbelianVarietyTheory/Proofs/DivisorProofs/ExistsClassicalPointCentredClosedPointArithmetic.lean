import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBirationalModelSemiAbelianAmpleFrames
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem flat_and_lft_toInt {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [h : ArithBase o Ω] (M : RatModel o Ω) :
    Flat (M.s ≫ spMap (algebraMap ℤ o)) ∧ LocallyOfFiniteType (M.s ≫ spMap (algebraMap ℤ o)) := by
  have := h.ded
  have hΩ := h.char
  have : CharZero o := ⟨fun a b hab => by
    have := congrArg (algebraMap o Ω) hab
    simpa using this⟩
  have hft := h.ft
  have := M.lft
  have : Flat M.s := GlobalTheory.ModelOfOutput.flat_ratModel M
  have : Flat (spMap (algebraMap ℤ o)) :=
    Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : LocallyOfFiniteType (spMap (algebraMap ℤ o)) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 hft
  exact ⟨inferInstance, inferInstance⟩

theorem exists_cen (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω) (x : M.Z)
    (hx : IsClosed ({x} : Set M.Z)) (U : M.Z.Opens) (hU : (U : Set M.Z).Nonempty) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U x y := by
  obtain ⟨h1, h2⟩ := flat_and_lft_toInt M
  exact GlobalTheory.padicAlgCl_integral_points.1 M.Z (M.s ≫ spMap (algebraMap ℤ o)) x hx U hU

theorem exists_cen_main : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω) (x : M.Z),
    IsClosed ({x} : Set M.Z) → ∀ U : M.Z.Opens, (U : Set M.Z).Nonempty →
      ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U x y :=
  fun o Ω _ _ _ _ M x hx U hU => exists_cen o Ω M x hx U hU

end GlobalTheory.Poinc
