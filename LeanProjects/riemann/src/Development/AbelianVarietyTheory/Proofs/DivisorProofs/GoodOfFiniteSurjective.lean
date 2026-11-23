import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwist
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.FiniteSurjDim

theorem eq_of_finite_surjective {k : Type} [Field k] {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Surjective f]
    (p : Y ⟶ Spec (CommRingCat.of k)) [Nonempty X] {a b : ℕ} (ha : SmoothOfRelativeDimension a (f ≫ p))
    (hb : SmoothOfRelativeDimension b p) : a = b := by
  have : Nonempty Y := ⟨f (Classical.arbitrary X)⟩
  have h1 := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth (f ≫ p) a ha
  have h2 := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth p b hb
  have c1 : topologicalKrullDim Y ≤ topologicalKrullDim X :=
    GlobalTheory.PosBaseChange.dim_le_of_isClosedMap f.isClosedMap f.surjective
  have c2 : topologicalKrullDim X ≤ topologicalKrullDim Y :=
    GlobalTheory.PosBaseChange.dim_le_of_isDiscrete f.continuous fun y => f.isDiscrete_preimage_singleton y
  rw [h1, h2] at c1 c2
  exact_mod_cast le_antisymm c2 c1

end GlobalTheory.FiniteSurjDim
