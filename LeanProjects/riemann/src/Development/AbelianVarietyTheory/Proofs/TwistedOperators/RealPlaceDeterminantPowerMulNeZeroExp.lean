import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ApplyMulTorProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.THProvA
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ConjHol

theorem detPow_mul_ne_zero_exp : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (m : D.what₂.Tau → ℤ), (∀ a b, detPow θ V m (a * b) = detPow θ V m a * detPow θ V m b) ∧ (∀ a, detPow θ V m a ≠ 0) ∧ (∀ Y : GlobalTheory.SmoothForms.LieN V, detPow θ V m (GlobalTheory.SmoothForms.expInf θ V Y) = cexp (GlobalTheory.AdSpan.ConjHol.trLin V m Y)) := by
  intro D θ hθ V m
  have R : GlobalTheory.SmoothForms.RealPoints θ V := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  have hd : ∀ a, detPow θ V m a = ∏ ρ, (infMat D.sp.cm.sig V.gram (θ ρ) a).det ^ (m ρ) := fun a => rfl
  refine ⟨fun a b => ?_, fun a => ?_, fun Y => ?_⟩
  · rw [hd, hd, hd, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun ρ _ => ?_
    rw [R.2.2.2.1, det_mul, mul_zpow]
  · rw [hd]
    refine Finset.prod_ne_zero_iff.2 fun ρ _ => zpow_ne_zero _ fun h0 => ?_
    have h : (infMat D.sp.cm.sig V.gram (θ ρ) a)ᴴ * gramAt D V ρ * infMat D.sp.cm.sig V.gram (θ ρ) a = gramAt D V ρ :=
      GlobalTheory.RealLift.archM_mem hθ V a ρ
    have h2 := congrArg det h
    rw [det_mul, h0, mul_zero] at h2
    exact (R.1 ρ).2.ne_zero h2.symm
  · rw [hd]
    change _ = cexp (∑ ρ, (m ρ : ℂ) * trace (Y ρ).1)
    rw [Complex.exp_sum]
    refine Finset.prod_congr rfl fun ρ _ => ?_
    rw [(GlobalTheory.SmoothForms.isExpFam_expInf R Y).2 ρ, Formalism.MainNotions.DIV.Inh.det_exp, Complex.exp_int_mul]

end GlobalTheory.AdSpan.ConjHol
