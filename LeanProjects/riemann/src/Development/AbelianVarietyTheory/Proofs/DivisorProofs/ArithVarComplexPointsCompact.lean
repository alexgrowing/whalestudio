import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapSumSwap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictChernPart
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyIntEqZeroOfIsHomogeneous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZero
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open ReciprocityTheory.AnForm.M GlobalTheory.ChernPoly

namespace GlobalTheory

theorem IsArithVar.finite_emb_and_topology : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {D : ℕ}, IsArithVar p D →
    Finite (k →+* ℂ) ∧ ∀ σ : k →+* ℂ, CompactSpace (CxPts p σ) ∧ T2Space (CxPts p σ) ∧
      SecondCountableTopology (CxPts p σ) := fun h =>
  ⟨h.finite_emb, fun σ => ⟨h.compactSpace σ, CxPts.t2Space_cxPts_of_isProjOver σ h.isProjOver,
    CxPts.secondCountableTopology_of_isProjOver σ h.isProjOver⟩⟩

end GlobalTheory
