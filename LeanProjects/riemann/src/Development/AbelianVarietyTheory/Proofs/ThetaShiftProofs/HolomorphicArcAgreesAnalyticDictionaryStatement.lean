import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicArcAgreesAnalyticDictionary
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicArc_agrees_analyticDictionary : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (Λ : GtAn₀ a), letI := H.starRing; ∃ (gam : (Fu.Di Ha.i).La ≃ₗ[𝓞 E] Λ.A.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] Λ.A.V), (∀ z, Λ.ex₀ (h z) = Ha.ex₀ z) ∧ (∀ v, Λ.y (gam v) = Ha.y v) ∧ (∀ w v, h (Ha.Pw w v) = Λ.A.Pw w (gam v)) ∧ ∀ v v', Λ.A.EF (gam v) (gam v') = (Fu.Di Ha.i).EF v v' := by
  first | exact @GlobalTheory.ArcCompare.holArc_agrees | exact GlobalTheory.ArcCompare.holArc_agrees | (intros; apply GlobalTheory.ArcCompare.holArc_agrees <;> assumption)
