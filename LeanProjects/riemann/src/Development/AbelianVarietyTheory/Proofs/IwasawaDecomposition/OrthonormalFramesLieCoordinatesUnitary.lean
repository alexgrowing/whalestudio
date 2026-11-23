import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HodgeGramEqRiemann
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaPointsFrameRatio
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyUnifWitnessDataOfIsUnf
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.ShFam
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam

theorem lie_coord_unitary : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r}, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (x x₁ : (U.X k).dom), IsOrth (U.X k) x.1 → IsOrth (U.X k) x₁.1 → (U.un k x₁).x = (U.un k x).x → ∀ (τ : E →+* ℂ) (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ), (∀ b, Formalism.L2.Pj.IsCombAt (U.un k x).x ((U.un k x).u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => (T b' b : ℂ)) ((U.un k x₁).u τ b)) → Tᴴ * T = 1 := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U hσ hU k x x₁ hx hx₁ e τ T hT
  obtain ⟨W⟩ := GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf E H Dw l Xo c σ r _ hU
  obtain ⟨d, hd0, hd⟩ := GlobalTheory.HodgeSmooth.exists_diag_riem hσ hU W
  obtain ⟨Hm, -, -, hH⟩ := (W.period k x₁).2.2.2.2
  obtain ⟨hPx, hv⟩ := W.lie k x₁
  have h1 := hd k x₁ hx₁ (W.ik k) (W.Pm k x₁) (W.period k x₁) Hm hH hPx.symm τ _ ((U.un k x₁).u τ) 1 (hv τ)
    (fun b => by
      convert GlobalTheory.isCombAt_single_of_isTanAt (U.un k x₁).x ((U.un k x₁).u τ) ((U.un k x₁).tan τ) b using 1
      show (fun b' => (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) b' b) = Pi.single b 1
      funext b'
      rw [Matrix.one_apply, Pi.single_apply])
  have h2 := hd k x hx (W.ik k) (W.Pm k x₁) (W.period k x₁) Hm hH (hPx.symm.trans e) τ _ ((U.un k x₁).u τ) T
    (hv τ) hT
  have h3 : d k τ • (Tᴴ * T) = d k τ • (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) := by
    rw [← h2, h1, conjTranspose_one, Matrix.mul_one]
  exact smul_right_injective _ (hd0 k τ) h3

end GlobalTheory.ShFam
