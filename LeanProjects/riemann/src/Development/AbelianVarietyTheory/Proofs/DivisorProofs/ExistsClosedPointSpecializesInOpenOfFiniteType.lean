import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefIsPsEffAndBigTensNef
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory

theorem closedPoint_specializing_in_open : ∀ (k : Type) [Field k] (X : Scheme.{0}) (q : X ⟶ Sp k) [LocallyOfFiniteType q] (U : X.Opens) (y : X), y ∈ U → ∃ x : X, IsClosed ({x} : Set X) ∧ y ⤳ x ∧ x ∈ U := by
  intro k _ X q _ U y hy
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace q
  have hne : (closure ({y} : Set X) ∩ (U : Set X)).Nonempty := ⟨y, subset_closure rfl, hy⟩
  have hlc : IsLocallyClosed (closure ({y} : Set X) ∩ (U : Set X)) :=
    ⟨U, closure {y}, U.isOpen, isClosed_closure, Set.inter_comm _ _⟩
  obtain ⟨x, ⟨hxc, hxU⟩, hx⟩ := nonempty_inter_closedPoints hne hlc
  exact ⟨x, (mem_closedPoints_iff).1 hx, specializes_iff_mem_closure.2 hxc, hxU⟩

end GlobalTheory
