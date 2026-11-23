import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfFormallyUnramifiedStandardSmoothSameRelDi
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_of_formallyUnramified_standardSmooth_same_relDim : ∀ (A B C : Type) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (g : ℕ), Algebra.IsStandardSmoothOfRelativeDimension g A B → Algebra.IsStandardSmoothOfRelativeDimension g A C → Algebra.FormallyUnramified B C → Algebra.Etale B C := by
  first | exact @GlobalTheory.etale_of_formallyUnramified_of_relDim | exact GlobalTheory.etale_of_formallyUnramified_of_relDim | (intros; apply GlobalTheory.etale_of_formallyUnramified_of_relDim <;> assumption)
