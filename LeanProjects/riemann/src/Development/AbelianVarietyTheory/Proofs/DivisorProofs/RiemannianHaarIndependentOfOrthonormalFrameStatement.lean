import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemannianHaar_independent_of_orthonormal_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 p1 : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x y : Frame Ψ r), (∀ a b, cc (G a b) = G b a) → (∀ τ : Ψ, gram τ.1 G (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) → (∀ τ : Ψ, gram τ.1 G (mat y τ) = Matrix.diagonal fun a : Fin r => ((sgn p1 (a : ℕ) : ℝ) : ℂ)) → riemHaar Ψ G x = riemHaar Ψ G y := by
  first | exact @GlobalTheory.FrameIndep.riemHaar_frame_indep | exact GlobalTheory.FrameIndep.riemHaar_frame_indep | (intros; apply GlobalTheory.FrameIndep.riemHaar_frame_indep <;> assumption)
