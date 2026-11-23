import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagValuePullbackCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOnRegularFlagged
open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.MixDens GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Published
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_value_pullback_cover : ArCalc → ∀ (k : Type) [CommRing k] (B₀ B : Scheme.{0}) [IsIntegral B₀] [IsIntegral B] (q₀ : B₀ ⟶ Sp k) (q : B ⟶ Sp k) (e : ℕ), IsArithVar q₀ (e + 1) → ∀ (β : B ⟶ B₀) (w : β ≫ q₀ = q), FlagChain.IsCov q₀ (e + 1) β → ∀ (L : B₀.Modules) (g : ℕ) (h : VMetric q₀ L g) (H : h.IsCInf) (F₀ : FlagSp L g) (F₁ : FlagSp ((Scheme.Modules.pullback β).obj L) g) (N : HermLB q₀) (a : ℝ), F₀.IsVal H N (genericPoint B₀) e a → F₁.IsVal (H.pull β w) (N.pull β w) (genericPoint B) e ((β.residueDegree (genericPoint B) : ℝ) * a) := by
  first | exact @GlobalTheory.FlagCoverVal.isVal_pull | exact GlobalTheory.FlagCoverVal.isVal_pull | (intros; apply GlobalTheory.FlagCoverVal.isVal_pull <;> assumption)
