import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefDominantWeightPositivity
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfCurveDegreesNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfSurjectivePullback
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.TrueGeo
open scoped ENNReal Classical
open Limits

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nef_dominant_weight_positivity : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y) (h : O.Reads A T H),
  ∀ (B : ℝ), 2 ≤ B → ∀ (w : Wt O.Y), WeightThresholdDefs.Dominant O.Y w → NefCond O.Y B w →
  ∀ (c : O.s.Comp) (X' : Scheme.{0}) (p' : X' ⟶ Sp (𝓞 D.what₂.LL)), IsProjOver p' →
  ∀ (ρ : X' ⟶ (h.mdl (FlagAr.setB O.Y B) c).V.X) (hρ : ρ ≫ (h.mdl (FlagAr.setB O.Y B) c).V.p = p')
    (q : ℕ) [Fact q.Prime], q ∉ FlagAr.setB O.Y B →
  ∀ (Z : Scheme.{0}) (i : Z ⟶ X') [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod q) Γ(Z, ⊤)],
    topologicalKrullDim Z = 1 →
    0 ≤ ∑ x, -(w x.1 x.2) *
      (topSelfIntersection (ZMod q) ((((h.mdl (FlagAr.setB O.Y B) c).root (FlagAr.setB O.Y B) x).pull ρ hρ).B.pull i) 1 : ℝ) := by
  first | exact @GlobalTheory.NefDeRhamRoots.nonneg_roots | exact GlobalTheory.NefDeRhamRoots.nonneg_roots | (intros; apply GlobalTheory.NefDeRhamRoots.nonneg_roots <;> assumption)
