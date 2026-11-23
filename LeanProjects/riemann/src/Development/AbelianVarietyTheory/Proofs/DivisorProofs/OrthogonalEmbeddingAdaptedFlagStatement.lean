import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalEmbeddingAdaptedFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOnRegularFlagged
open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.MixDens GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Published
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonal_embedding_adapted_flag : Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (ι : Type) [Fintype ι] (L : X.Modules) (g : ℕ) (hL : VMetric p L g), hL.IsCInf → ∀ (E : ι → X.Modules) (r : ι → ℕ) (h : ∀ a, VMetric p (E a) (r a)), (∀ a, (h a).IsCInf) → ∀ (T : ∀ a, E a ⟶ L) (fl : ∀ a, Vert.Flag (E a) (r a)) (w : Vert.Flag L g) (e : (Σ a, Fin (r a)) ≃ Fin g), OrthEmb hL h T → Adapted T fl w e → ∀ (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (τ : Y ⟶ X) (v : τ ≫ p = q) (d : ℕ), IsArithVar q (d + 1) → ∀ N : HermLB q, bcPair (hL.pull τ v) (w.pull τ) N d = ∑ a, bcPair ((h a).pull τ v) ((fl a).pull τ) N d := by
  first | exact @GlobalTheory.OrthBcSum.bcPair_pull_eq_sum | exact GlobalTheory.OrthBcSum.bcPair_pull_eq_sum | (intros; apply GlobalTheory.OrthBcSum.bcPair_pull_eq_sum <;> assumption)
