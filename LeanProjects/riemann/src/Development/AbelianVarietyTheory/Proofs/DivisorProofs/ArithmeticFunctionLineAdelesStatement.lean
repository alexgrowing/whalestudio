import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticFunctionLineAdeles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOnRegularFlagged
open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.MixDens GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Published
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_function_line_adeles : ArCalc → ArDegree → ∀ (D : D7) (O : Setup D), O.Core → ∀ R : ℝ, 2 ≤ R → ∀ (c : O.s.Comp) (V : Cover (O.var c)) (x x' : Letter O.S.Dw → HermLB V.p), (∀ z : Letter O.S.Dw, V.Induces (lineAdl O R c (.inl (z.1, z.2)) 1) (x z) 1) → (∀ (k : ℕ) (z : Letter O.S.Dw), (letters O.S.Dw)[k]? = some z → V.Induces (lineAdl O R c (.inr k) 1) (x' z) 1) → ∀ Φ : MvPolynomial (Letter O.S.Dw ⊕ Letter O.S.Dw) ℝ →ₗ[ℝ] ℝ, IsArFun (Sum.elim x x') (O.var c).dim Φ → termW O c R = Φ (pairPol O.S.Dw.mult (dimGr D.what₂.Tau O.N O.j - 1)) / ((∏ σ, ((O.S.Dw.mult σ).factorial : ℝ)) * V.ν) := by
  first | exact @GlobalTheory.DRRead.termW_read | exact GlobalTheory.DRRead.termW_read | (intros; apply GlobalTheory.DRRead.termW_read <;> assumption)
