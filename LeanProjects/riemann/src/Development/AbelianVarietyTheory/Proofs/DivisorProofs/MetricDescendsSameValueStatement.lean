import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricDescendsSameValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOnRegularFlagged
open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.MixDens GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Published
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metric_descends_same_value : ∀ (k k' : Type) [CommRing k] [CommRing k'] (φ : k ≃+* k') (X : Scheme.{0}) (p : X ⟶ Sp k') (d : ℕ), IsArithVar p d → ∀ (E : X.Modules) (r : ℕ) (h : VMetric p E r) (H : h.IsCInf), IsArithVar (p ≫ spMap φ.toRingHom) d ∧ ∃ (h₀ : VMetric (p ≫ spMap φ.toRingHom) E r) (H₀ : h₀.IsCInf), SameMet φ h h₀ ∧ ∀ (F : FlagSp E r) (z : X) (e : ℕ) (a : ℝ), F.IsVal H (VMetric.det H) z e a → F.IsVal H₀ (VMetric.det H₀) z e a := by
  first | exact @GlobalTheory.BaseIso.exists_sameMet | exact GlobalTheory.BaseIso.exists_sameMet | (intros; apply GlobalTheory.BaseIso.exists_sameMet <;> assumption)
