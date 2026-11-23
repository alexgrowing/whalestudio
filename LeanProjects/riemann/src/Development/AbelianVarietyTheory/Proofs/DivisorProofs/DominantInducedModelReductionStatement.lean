import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DominantInducedModelReduction
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfCurveDegreesNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfSurjectivePullback
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.TrueGeo
open scoped ENNReal Classical
open Limits

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominant_induced_model_reduction : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y) (h : O.Reads A T H),
  ∀ (B : ℝ), 2 ≤ B → ∀ (u : Wt O.Y) (s : ℚ), IsRat O.Y u → 0 < s → WeightThresholdDefs.Dominant O.Y (A.sh u s) →
  ∀ (c : O.s.Comp) (M : TrueGeo.Model (O.var c)) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 D.what₂.LL) → ℝ),
  (O.Mb B u s c).Induced M L k cf → ∀ (q : ℕ) [Fact q.Prime],
  ∃ (X' : Scheme.{0}) (p' : X' ⟶ Sp (𝓞 D.what₂.LL)) (π : X' ⟶ M.X) (hπ : π ≫ M.p = p')
    (ρ : X' ⟶ (h.mdl (FlagAr.setB O.Y B) c).V.X) (hρ : ρ ≫ (h.mdl (FlagAr.setB O.Y B) c).V.p = p'),
    IsProjOver p' ∧ Function.Surjective π ∧ ∃ (κ a : ℝ), 0 < κ ∧ 0 ≤ a ∧
    ∀ (Z : Scheme.{0}) (i : Z ⟶ X') [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod q) Γ(Z, ⊤)],
      topologicalKrullDim Z = 1 →
      κ * (topSelfIntersection (ZMod q) ((L.pull π hπ).B.pull i) 1 : ℝ) =
        a * (topSelfIntersection (ZMod q) (((h.mdl (FlagAr.setB O.Y B) c).amp.pull ρ hρ).B.pull i) 1 : ℝ) +
        ∑ x, -(A.sh u s x.1 x.2) *
          (topSelfIntersection (ZMod q) ((((h.mdl (FlagAr.setB O.Y B) c).root (FlagAr.setB O.Y B) x).pull ρ hρ).B.pull i) 1 : ℝ) := by
  first | exact @GlobalTheory.NefDeRhamCover.exists_cover_degree_eq | exact GlobalTheory.NefDeRhamCover.exists_cover_degree_eq | (intros; apply GlobalTheory.NefDeRhamCover.exists_cover_degree_eq <;> assumption)
