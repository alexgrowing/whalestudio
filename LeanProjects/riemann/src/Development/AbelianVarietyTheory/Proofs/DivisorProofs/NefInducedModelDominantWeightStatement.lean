import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefInducedModelDominantWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfCurveDegreesNonneg
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.TrueGeo
open scoped ENNReal Classical
open Limits

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nef_induced_model_dominant_weight : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y), O.Reads A T H →
  ∀ (B : ℝ), 2 ≤ B → ∀ (u : Wt O.Y) (s : ℚ), IsRat O.Y u → 0 < s → WeightThresholdDefs.Dominant O.Y (A.sh u s) → NefCond O.Y B (A.sh u s) →
  ∀ (c : O.s.Comp) (M : TrueGeo.Model (O.var c)) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 D.what₂.LL) → ℝ),
  (O.Mb B u s c).Induced M L k cf → ∀ (q : ℕ) [Fact q.Prime], q ∉ FlagAr.setB O.Y B →
  ∃ (N : TrueGeo.Model (O.var c)) (π : N.X ⟶ M.X) (hπ : π ≫ M.p = N.p), Function.Surjective π ∧
    ∀ (Z : Scheme.{0}) (i : Z ⟶ N.X) [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod q) Γ(Z, ⊤)],
      topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod q) ((L.pull π hπ).B.pull i) 1 := by
  first | exact @GlobalTheory.NefDeRhamCore.exists_model_nonneg | exact GlobalTheory.NefDeRhamCore.exists_model_nonneg | (intros; apply GlobalTheory.NefDeRhamCore.exists_model_nonneg <;> assumption)
