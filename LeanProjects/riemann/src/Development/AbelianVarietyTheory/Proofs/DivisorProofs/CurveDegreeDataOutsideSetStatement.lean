import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveDegreeDataOutsideSet
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfCurveDegreesNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfSurjectivePullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsumSmul
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.TrueGeo
open scoped ENNReal Classical
open Limits

theorem _root_.GlobalTheory.T.curve_degree_data_outside_set : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y) (h : O.Reads A T H),
  ∀ (B : ℝ), 2 ≤ B → ∀ (c : O.s.Comp) (q : ℕ) [Fact q.Prime], q ∉ FlagAr.setB O.Y B →
  ∀ (Z : Scheme.{0}) (i : Z ⟶ (h.mdl (FlagAr.setB O.Y B) c).V.X) [IsClosedImmersion i] [IsIntegral Z]
    [Algebra (ZMod q) Γ(Z, ⊤)], topologicalKrullDim Z = 1 →
    GlobalTheory.PowerSumSmul.DegData O.j (q : ℝ) (fun (τ : D.what₂.Tau) (k : Fin O.N) =>
      (topSelfIntersection (ZMod q) (((h.mdl (FlagAr.setB O.Y B) c).root (FlagAr.setB O.Y B) (τ, k)).B.pull i) 1 : ℝ)) := by
  first | exact @GlobalTheory.DegreeRootData.degData | exact GlobalTheory.DegreeRootData.degData | (intros; apply GlobalTheory.DegreeRootData.degData <;> assumption)
