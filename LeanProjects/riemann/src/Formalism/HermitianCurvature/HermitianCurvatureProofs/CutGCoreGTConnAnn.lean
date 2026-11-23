import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_GCore_GTConnCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtBrReal

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Complex

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem annulus_condition_holds : GTCAnnulus := by
  intro TT α hTT hα hcurv hper
  have hhol : ∃ n : ℤ, (circleIntegral α 0 (TT + 1)).im = Real.pi * n :=
    hper (TT + 1) (by linarith) (by nlinarith [sq_nonneg (TT + 1 / 2)])
  have hcurv' : ∀ ζ : ℂ, TT < Complex.normSq ζ → (Ann.wZb α ζ).re = 0 := hcurv
  refine ⟨Ann.uu TT α, Ann.contDiffOn_uu hTT hα hcurv' hhol, fun ζ hζ => ?_⟩
  obtain ⟨h1, h2⟩ := Ann.wZ_uu hTT hα hcurv' hhol (ζ := ζ) hζ
  have hn : ‖Ann.uu TT α ζ‖ = 1 := Ann.norm_uu ζ
  have hs : star (Ann.uu TT α ζ) * Ann.uu TT α ζ = 1 := by
    calc star (Ann.uu TT α ζ) * Ann.uu TT α ζ
        = (starRingEnd ℂ) (Ann.uu TT α ζ) * Ann.uu TT α ζ := rfl
      _ = ((‖Ann.uu TT α ζ‖ : ℝ) : ℂ) ^ 2 := Complex.conj_mul' _
      _ = 1 := by rw [hn]; norm_num
  refine ⟨hn, ?_, ?_⟩
  · show star (Ann.uu TT α ζ) * Ann.wZ (Ann.uu TT α) ζ = α ζ
    rw [h1, ← mul_assoc, hs, one_mul]
  · show star (Ann.uu TT α ζ) * Ann.wZb (Ann.uu TT α) ζ = -star (α ζ)
    rw [h2, mul_neg, ← mul_assoc, hs, one_mul] <;> rfl

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
