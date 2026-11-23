import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjModelClosedFiberIntegral
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
theorem _root_.GlobalTheory.T.proj_model_closed_fiber_integral : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y) (h : O.Reads A T H),
  ∀ (P : Finset ℕ) (c : O.s.Comp) (X' : Scheme.{0}) (p' : X' ⟶ Sp (𝓞 D.what₂.LL)), IsProjOver p' →
  ∀ (ρ : X' ⟶ (h.mdl P c).V.X) (hρ : ρ ≫ (h.mdl P c).V.p = p') (r : ℕ) [Fact r.Prime]
    (Z : Scheme.{0}) (i : Z ⟶ X') [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod r) Γ(Z, ⊤)],
    topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod r) (((h.mdl P c).amp.pull ρ hρ).B.pull i) 1 := by
  first | exact @GlobalTheory.AmpNefFib.main | exact GlobalTheory.AmpNefFib.main | (intros; apply GlobalTheory.AmpNefFib.main <;> assumption)
