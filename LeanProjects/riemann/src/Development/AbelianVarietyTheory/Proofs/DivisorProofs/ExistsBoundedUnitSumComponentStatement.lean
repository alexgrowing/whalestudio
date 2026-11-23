import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedUnitSumComponent
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSuppOnIffIdemMulOfNatural
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_boundedUnit_sum_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (ι : Type) [Fintype ι] (G : ι → WTZ E), (∀ i, Even (G i).2) → (∀ i, ∃ s t : Rul Xo c, (s ∈ GlobalTheory.AllWt.secZ Xo c (Formalism.L2.Pj.exZ Dw (G i)) ∧ t ∈ GlobalTheory.AllWt.secZ Xo c (-Formalism.L2.Pj.exZ Dw (G i)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * t = t ∧ s * t = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ framesOn (U σ) Z, GlobalTheory.AllWt.homN (U σ) (x) (G i) s z ≤ C ∧ GlobalTheory.AllWt.homN (U σ) (x) (-(G i)) t z ≤ C)) ∧ ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : c.F) • s) ∧ 0 ≤ v ((m : c.F) • t)) → ∀ n : ι → ℤ, ∃ s t : Rul Xo c, (s ∈ GlobalTheory.AllWt.secZ Xo c (Formalism.L2.Pj.exZ Dw (∑ i, n i • G i)) ∧ t ∈ GlobalTheory.AllWt.secZ Xo c (-Formalism.L2.Pj.exZ Dw (∑ i, n i • G i)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * t = t ∧ s * t = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ framesOn (U σ) Z, GlobalTheory.AllWt.homN (U σ) (x) (∑ i, n i • G i) s z ≤ C ∧ GlobalTheory.AllWt.homN (U σ) (x) (-(∑ i, n i • G i)) t z ≤ C)) ∧ ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : c.F) • s) ∧ 0 ≤ v ((m : c.F) • t) := by
  first | exact @GlobalTheory.FlatUnitProd.exists_unit_sum | exact GlobalTheory.FlatUnitProd.exists_unit_sum | (intros; apply GlobalTheory.FlatUnitProd.exists_unit_sum <;> assumption)
