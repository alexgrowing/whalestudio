import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointPoly
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernTopFormNegativePartEqZeroOfNonnegOnOpenStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernTopPointClassHodgeMetricLieNonnegStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricPointClassFormMassEqCovolumeStatement

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

namespace GlobalTheory.LieBase

theorem hasChernIntegral_pointPoly_covol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → HasChernIntegral Eb (openPart j) (lieGram e U hj f₀ A₀) (pointPoly H Dw) (GlobalTheory.TrueCx.covol (U.X k)) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL
  have h0 := GlobalTheory.T.chernTopForm_negativePart_eq_zero_of_nonneg_on_open Eb (openPart j) (lieGram e U hj f₀ A₀) (pointPoly H Dw)
    (GlobalTheory.T.chernTop_pointClass_hodge_metric_lie_nonneg E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL)
  have h1 := GlobalTheory.T.hodgeMetric_pointClassForm_mass_eq_covolume E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL
  have hc := (GlobalTheory.TrueCx.covol_pos (U.X k)).le
  refine ⟨fun ε => ?_, ?_⟩
  · rcases Int.units_eq_one_or ε with rfl | rfl
    · rw [h1]; exact ENNReal.ofReal_ne_top
    · rw [h0]; exact ENNReal.zero_ne_top
  · rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def, h1, h0, ENNReal.toReal_ofReal hc]; simp

end GlobalTheory.LieBase
