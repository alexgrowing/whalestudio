import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.Unf.StepFour

variable {D : D7}

theorem zEll_mem_ratMx (T : HSp D) (ρ : ℕ) (z : Fin T.rank → D.host.E) : zEll T ρ z ∈ ratMx D T.rank ρ := by
  refine ⟨Matrix.vecMulVec z (fun i : Fin ρ => if i.1 + 1 = ρ then (1 : D.host.E) else 0), ?_⟩
  funext i j
  change incA D (z i * (if j.1 + 1 = ρ then (1 : D.host.E) else 0)) = ratV z i * ell D ρ j
  simp only [ratV, ell]
  split_ifs <;> simp

theorem incAdj_yZero_mem {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (z : Fin S.rank → D.host.E) :
    d.incAdj S (yZero S ρ z) ∈ ratMx D T.rank S.rank := by
  have hy : yZero S ρ z ∈ ratMx D S.rank ρ := by
    rw [yZero]; exact neg_mem (zEll_mem_ratMx S ρ z)
  rw [HypDec.incAdj_apply, HypDec.incY_apply]
  exact ratMx_mul (rat_mem _) (ratMx_smul _ (ratMx_mul (ratMx_adj hy) (rat_mem _)))

theorem star_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (x : AF D.host.F) :
    star (ψ x) = ψ (-x) := by
  change (starRingEnd ℂ) (ψ x) = _
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.1.2.1 x)]

end GlobalTheory.Unf.StepFour
end

noncomputable section
namespace GlobalTheory.Unf.StepFour

variable {D : D7}

theorem integrand_eq {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V V₀ W W₀ : HSp D} {ρ : ℕ}
    (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (z : Fin V₀.rank → D.host.E) (f : WO V₀ W → ℂ)
    (hf : IsThetaFunO ψ V₀ W f) (b : Mx D ρ V₀.rank) :
    star (psiBes ψ dV 1 z (dV.nB b)) * f (xZero dW ⬝ b) =
      heisO ψ V₀ W (dW.incX V₀ b) (heisO ψ V₀ W (dW.incAdj V₀ (yZero V₀ ρ z)) (heisO ψ V₀ W (dW.inc0 V₀ 0) f)) 0 := by
  rw [HypDec.integrandT_eq, ← psi_yZero ψ dV dW z b, star_psi hψ, map_zero, add_zero]
  obtain ⟨γ, hγ⟩ := incAdj_yZero_mem dW V₀ z
  have hx : dW.incX V₀ b = xZero dW ⬝ b := rfl
  have hq := hf.quasi γ (xZero dW ⬝ b)
  rw [show ratW W V₀ γ = dW.incAdj V₀ (yZero V₀ ρ z) from hγ] at hq
  rw [hx, add_comm (xZero dW ⬝ b), hq, ← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  have hc : algebraMap D.host.F (AF D.host.F) (1 / 2) + algebraMap D.host.F (AF D.host.F) (1 / 2) = 1 := by
    rw [← map_add, add_halves, map_one]
  have hs : symplO V₀ W (xZero dW ⬝ b) (dW.incAdj V₀ (yZero V₀ ρ z)) =
      -symplO V₀ W (dW.incAdj V₀ (yZero V₀ ρ z)) (xZero dW ⬝ b) := GlobalTheory.OrientedHeis.symplO_skew _ _
  rw [symplOH, symplOH]
  linear_combination (symplO V₀ W (dW.incAdj V₀ (yZero V₀ ρ z)) (xZero dW ⬝ b)) * hc -
    algebraMap D.host.F (AF D.host.F) (1 / 2) * hs

end GlobalTheory.Unf.StepFour
end

noncomputable section
namespace GlobalTheory.Unf.StepFour

theorem fl_eq_flatBF : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J)
    (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ →
      fl ψ B.d J.W s.vS s.vT s.vU (fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n)) (xZero J.d) Ψ = flatBF s Ψ 0 := by
  intro D ψ ρ B J s Ψ hΨ
  have hψ : IsStdChar D ψ (-1) := s.weil.std
  have hf : ∀ x, IsThetaFunO ψ B.V₀ J.W (B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ x) := fun x =>
    (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hψ).1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ x
  unfold fl flatBF flat flatAt
  congr 1
  funext u
  simp only [flFun, flatFun, evalAt, HypDec.mixT]
  have hu : ∀ b, star (psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b * B.d.levi u.1)) =
      star (psiUni ψ u.1) * star (psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b)) := by
    intro b
    rw [psiBes_mul B.d ψ 1 _ (B.d.nB_mem_NFlag b) (B.d.levi_mem_NFlag (mem_UX.1 u.2)), psiBes_levi, star_mul',
      mul_comm]
  simp_rw [hu, mul_assoc]
  rw [integral_const_mul]
  congr 1
  congr 1
  funext b
  exact integrand_eq hψ B.d J.d _ _ (hf _) b

end GlobalTheory.Unf.StepFour
end
