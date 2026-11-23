import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtAlong
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.MBLow

theorem hypS_of_isPolFibre : ∀ (K K' : Type) [Field K] [Field K'] (f : K →+* K') (P : PolAV (Sp K)) (P' : PolAV (Sp K')) (ψ : P'.A.left ⟶ P.A.left), IsPolFibre f P P' ψ → (letI := P.isAb.comm; GlobalTheory.ZH.HypS P.A P.L) → (letI := P'.isAb.comm; GlobalTheory.ZH.HypS P'.A P'.L) := by
  intro K K' _ _ f P P' ψ h hS
  letI := P.isAb.comm
  letI := P'.isAb.comm
  exact GlobalTheory.SymBaseChange.hypS_baseChange _ _ P.A P'.A (spMap f) ψ P.L P'.L P.isLB P'.isLB h.2.1 h.2.2.symm hS
end GlobalTheory.MBLow
end
