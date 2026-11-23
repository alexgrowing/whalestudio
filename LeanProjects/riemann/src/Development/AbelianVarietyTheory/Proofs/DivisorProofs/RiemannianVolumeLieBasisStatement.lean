import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianVolumeLieBasis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemannian_volume_lie_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E), 2 ≤ r → IsOrth X x → (∀ i, (e i).trace = 0 ∧ ∀ u w, herm X.Gm (e i *ᵥ u) w + herm X.Gm u (e i *ᵥ w) = 0) → LinearIndependent (maximalRealSubfield E) e → riemLie X.Ψ X.Gm x = ENNReal.ofReal (Real.sqrt ‖∏ τ : X.Ψ, τ.1 (Matrix.of fun i j => Matrix.trace (e i * e j)).det‖) • formLie X.Ψ e := by
  first | exact @GlobalTheory.SUVol.LieMeas.riemLie_eq_smul_formLie | exact GlobalTheory.SUVol.LieMeas.riemLie_eq_smul_formLie | (intros; apply GlobalTheory.SUVol.LieMeas.riemLie_eq_smul_formLie <;> assumption)
