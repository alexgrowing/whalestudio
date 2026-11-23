import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightsSumToVolumeProportional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveClassDegreeComputations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegFlLamAPowVdmCl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeValueTendstoChernStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR

theorem GlobalTheory.CovTestDR.vdmVal_tendsto : GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → RegularAlteration → GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.Ch2HodgeVanishes →
    ∀ r : ℝ, Ch2Const r → OnObj fun _ O _ _ _ _ => Tendsto (vdmVal O.Y) atTop (𝓝 (-(2 * r * O.Y.vol * testI O.Y))) := by
  intro hS hX h2 hH hR hV r hr D O hc hf A T H h
  have e : Tendsto (vdmVal O.Y) atTop
      (𝓝 (r * O.Y.chern (lamA D.what₂.Tau O.Y.N O.Y.j ^ dimGr D.what₂.Tau O.Y.N O.Y.j * vdmCl D.what₂.Tau O.Y.N O.Y.j))) :=
    GlobalTheory.T.vandermonde_value_tendsto_chern hS hX h2 hH hR hV r hr D O hc hf A T H h
  have hp : Propor O.Y := (GlobalTheory.CompPropObj.main h2 hH D O hc hf A T H h).2.2
  haveI : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  have hpos : 1 ≤ dimGr D.what₂.Tau O.Y.N O.Y.j := by
    unfold dimGr
    exact Nat.mul_pos Fintype.card_pos (Nat.mul_pos O.Y.j_pos (by have := O.Y.j_lt; omega))
  have hc' : lamA D.what₂.Tau O.Y.N O.Y.j ^ dimGr D.what₂.Tau O.Y.N O.Y.j * fibPt D.what₂.Tau O.Y.N O.Y.j =
      lamA D.what₂.Tau O.Y.N O.Y.j * curveCl D.what₂.Tau O.Y.N O.Y.j := by
    unfold curveCl
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hpos]
  rw [hp, GlobalTheory.VdmFibre.degFl_lamA_pow_vdmCl D.what₂.Tau O.Y.N O.Y.j _ O.Y.j_lt.le, hc', GlobalTheory.FlagPoly.TestClass.degFl_lamA_mul] at e
  convert e using 2
  unfold testI
  ring
