import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfCurveDegreesNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfSurjectivePullback
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefAtOfPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefInducedModelDominantWeightStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.TrueGeo
open scoped ENNReal Classical
open Limits

namespace GlobalTheory.NefDeRhamAt

theorem nefAt_dR : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y), O.Reads A T H →
  ∀ (B : ℝ), 2 ≤ B → ∀ (u : Wt O.Y) (s : ℚ), IsRat O.Y u → 0 < s → WeightThresholdDefs.Dominant O.Y (A.sh u s) → NefCond O.Y B (A.sh u s) →
  ∀ (c : O.s.Comp) (M : TrueGeo.Model (O.var c)) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 D.what₂.LL) → ℝ),
  (O.Mb B u s c).Induced M L k cf → ∀ (Z : Scheme.{0}) (i : Z ⟶ M.X) [IsClosedImmersion i] [IsIntegral Z] (q : ℕ)
  [Fact q.Prime] [Algebra (ZMod q) Γ(Z, ⊤)], q ∉ FlagAr.setB O.Y B → topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod q) (L.B.pull i) 1 := by
  intro hX hP hH D O hO A T H hR B hB u s hu hs hdom hnef c M L k cf hI Z i _ _ q _ _ hq hd
  obtain ⟨N, π, hπ, hsurj, hN⟩ := GlobalTheory.T.nef_induced_model_dominant_weight hX hP hH D O hO A T H hR B hB u s hu hs hdom hnef c M L k cf hI q hq
  exact nefAt_of_pull _ M.X N.X M.p N.p M.ar.isProjOver N.ar.isProjOver π hπ hsurj L q hN Z i hd

end GlobalTheory.NefDeRhamAt
