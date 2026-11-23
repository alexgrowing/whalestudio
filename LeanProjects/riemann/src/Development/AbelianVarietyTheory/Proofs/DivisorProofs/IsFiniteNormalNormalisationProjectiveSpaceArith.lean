import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaFin

theorem isFinite_fromNormalization_and_normal : ∀ (o F : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [Field F] [CharZero F] (b : o →+* F) (n : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp F) (f : X ⟶ PSpace o n) [QuasiCompact f] [QuasiSeparated f], Function.Injective b → (∀ x : F, ∃ a d : o, b d ≠ 0 ∧ x * b d = b a) → Geo.Tor.IsNormalScheme X → IsSeparated s → LocallyOfFiniteType s → QuasiCompact s → f ≫ PSpace.str o n = s ≫ spMap b → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X), Set.Finite {y : Sp K ⟶ X | y ≫ s = x ≫ s ∧ y ≫ f = x ≫ f}) → IsFinite f.fromNormalization ∧ Geo.Tor.IsNormalScheme f.normalization := by
  intro o F _ _ _ _ _ _ b n X s f _ _ hinj hfrac hX _ _ _ hw _
  letI : Algebra o F := b.toAlgebra
  haveI : IsFractionRing o F := by
    refine ⟨fun d => ?_, fun x => ?_, fun {x y} h => ?_⟩
    · refine IsUnit.mk0 _ ?_
      change b d ≠ 0
      exact (map_ne_zero_iff b hinj).mpr (nonZeroDivisors.ne_zero d.2)
    · obtain ⟨a, d, hd, e⟩ := hfrac x
      refine ⟨⟨a, ⟨d, mem_nonZeroDivisors_of_ne_zero fun h0 => hd (by rw [h0, map_zero])⟩⟩, e⟩
    · exact ⟨1, by simpa using hinj h⟩
  haveI : CharZero o := ⟨fun m k h => by
    have := congrArg b h
    simp only [map_natCast] at this
    exact Nat.cast_injective this⟩
  haveI : IsDedekindDomain (CommRingCat.of o) := ‹IsDedekindDomain o›
  haveI : CharZero (CommRingCat.of o) := ‹CharZero o›
  haveI hN : GlobalTheory.IsNormalScheme X := GlobalTheory.IsNormalScheme.of_pred hX
  haveI : IsReduced X := isReduced_of_isReduced_stalk X
  haveI : IsProper (PSpace.str o n) := isProper_str o n
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  refine ⟨GlobalTheory.isFinite_fromNormalization_of_over_fractionRing (o := CommRingCat.of o) f
    (PSpace.str o n) F s hw, ?_⟩
  exact GlobalTheory.IsNormalScheme.pred _

end GlobalTheory.ThetaFin
