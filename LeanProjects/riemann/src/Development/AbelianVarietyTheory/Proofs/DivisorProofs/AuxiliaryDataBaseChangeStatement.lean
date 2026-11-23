import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryDataBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoUniformlyOfFamAt
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec GlobalTheory.MetFam GlobalTheory.ShFam GlobalTheory.Toroidal GlobalTheory.CxPts
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.auxiliary_data_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) [SmoothOfRelativeDimension Dw.dim (genStr Z)] (x : OddPrimesWithRootsOfUnity Z) (T : Scheme.{0}) (b : T ⟶ Z.X) (q : T ⟶ Sp (𝓞 c.F)), b ≫ Z.s = q → (∀ w : T, b w ∈ abLocus Z.t.G) → ∀ σ' : c.F →+* ℂ, ∃ ρ : CxPts q (σ'.comp (algebraMap (𝓞 c.F) c.F)) → ℝ, ∀ y, CInfAt ρ y ∧ ∃ yc : CxPts (genStr Z) σ', y.1 ≫ b = yc.1 ≫ genι Z ∧ ¬ LiesIn yc (genBd Z) ∧ ρ y = x.r σ' yc := by
  first | exact @GlobalTheory.BoundaryRSmooth.cInfAt_r_pull | exact GlobalTheory.BoundaryRSmooth.cInfAt_r_pull | (intros; apply GlobalTheory.BoundaryRSmooth.cInfAt_r_pull <;> assumption)
