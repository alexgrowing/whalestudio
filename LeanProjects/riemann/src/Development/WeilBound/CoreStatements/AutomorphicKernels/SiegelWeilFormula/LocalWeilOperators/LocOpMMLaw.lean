import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocForm
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Imports
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.StepMVal
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.ChiWPf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousUnitaryMultiplicativeEqArgPowStatement

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace SD

variable (d : SD σ)

theorem chiW_mul (w : InfinitePlace F) : ∀ z z' : ℂ, z ≠ 0 → z' ≠ 0 → d.chiW w (z * z') = d.chiW w z * d.chiW w z' :=
  d.chiW_mul_pf w

theorem chiW_cont (w : InfinitePlace F) : ContinuousOn (d.chiW w) {z : ℂ | z ≠ 0} :=
  d.chiW_cont_pf w

theorem chiW_norm (w : InfinitePlace F) : ∀ z : ℂ, z ≠ 0 → ‖d.chiW w z‖ = 1 := by
  intro z _
  by_cases h : IsUnit (d.uW w z)
  · rw [SD.chiW, dif_pos h]
    exact Circle.norm_coe _
  · rw [SD.chiW, dif_neg h, norm_one]

theorem chiW_pos (w : InfinitePlace F) : ∀ r : ℝ, 0 < r → d.chiW w (r : ℂ) = 1 :=
  d.chiW_pos_pf w

theorem chiW_form (w : InfinitePlace F) : ∃ k : ℤ, ∀ z : ℂ, z ≠ 0 → d.chiW w z = (z / (‖z‖ : ℂ)) ^ k :=
  GlobalTheory.T.continuous_unitary_multiplicative_eq_arg_pow (d.chiW w) (d.chiW_mul w) (d.chiW_cont w) (d.chiW_norm w) (d.chiW_pos w)

end SD

namespace RD

variable {d : SD σ} (R : RD d) (w : InfinitePlace F)

theorem stepM_val (hT : TAll) : ∀ (y : GR d.n) (a : Matrix (Fin d.n) (Fin d.n) ℂ), IsUnit a.det → mR y = mLoc a →
    R.StepOK w (R.ι w y) (fun f u => (d.chiW w a.det * (‖a.det‖ : ℂ) ^ d.m) * f (Matrix.of u * a)) id :=
  R.stepM_val_pf w hT

variable {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}

theorem locOp_mM_law (hT : TAll) (hG : GoodAwayEx) (hL : R.IsLocOp w L) :
    ∃ k : ℤ, ∀ (y : GR d.n) (a : Matrix (Fin d.n) (Fin d.n) ℂ), IsUnit a.det → mR y = mLoc a → ∀ f, IsSw f →
      L y f = fun u => (a.det / (‖a.det‖ : ℂ)) ^ k * (‖a.det‖ : ℂ) ^ d.m * f (Matrix.of u * a) := by
  obtain ⟨k, hk⟩ := d.chiW_form w
  refine ⟨k, fun y a ha hy f hf => ?_⟩
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
  obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
  have e1 := (hL y f hf).2 Ψ hΨ.1 Φ hΦ hT'
  have e2 := ((R.stepM_val w hT y a ha hy).2 Ψ hΨ.1).2 f hf Φ hΦ hT'
  rw [R.tens_cancel hΨ.1 hΨ.2.1 (e1.symm.trans e2), hk _ ha.ne_zero]
  rfl

end RD

end PositivityTheory.SiegelWeilFormula

end
