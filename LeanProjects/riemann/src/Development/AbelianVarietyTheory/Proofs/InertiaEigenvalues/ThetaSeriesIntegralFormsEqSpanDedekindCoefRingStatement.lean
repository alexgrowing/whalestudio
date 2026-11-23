import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesIntegralFormsEqSpanDedekindCoefRing
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeriesIntegralForms_eq_span_dedekindCoefRing : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → ∀ ψ : Twist D Circle, ψ.Good → B.admitted ψ.Q → ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (R : Type) [CommRing R] [IsDedekindDomain R] (φ : R →+* ℂ), Function.Injective φ → IsCoefRing σ emb φ.range →
  (∀ k : B.levJ ψ, ((B.levLam ψ k : ℂˣ) : ℂ) ∈ φ.range) → ∀ O : Subring ℂ, φ.range ≤ O →
  B.mtLat σ emb O ψ = Submodule.span O (B.mtLat σ emb φ.range ψ : Set (Bridge.Gf S → PolF D T.rank S.rank)) := by
  first | exact @GlobalTheory.FormsBaseChange.mtLat_eq_span | exact GlobalTheory.FormsBaseChange.mtLat_eq_span | (intros; apply GlobalTheory.FormsBaseChange.mtLat_eq_span <;> assumption)
