import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BndIUnits

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization

namespace GlobalTheory.CompanionTheory.GL2Factorization.Dual

theorem finAt_ti {n : ℕ} (v : Pl) (g : GL (Fin n) 𝔸[ℚ]) :
    finAt v (ti g) = GL2LocalData.tinv (finAt v g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h := congrArg (fun x : GL (Fin n) (Qv v) => x.val j i) (Reduction.finAt_inv v g)
  exact h

theorem finite_component_weyl_GL3 (v : Pl) : finAt v (w3 : G3) = GL2LocalData.w3 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> first | rfl | simp [w3, GL2LocalData.w3, Reduction.finAt_apply] <;> rfl

theorem finite_component_weyl_GL2 (v : Pl) : finAt v (w2 : G2) = GL2LocalData.w2 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> first | rfl | simp [w2, GL2LocalData.w2, Reduction.finAt_apply] <;> rfl

theorem gR_mul (g h : G3) : GP.gR (g * h) = GP.gR g * GP.gR h := by
  simp [GP.gR, Reduction.infAt_mul, map_mul]

theorem gR_inv (g : G3) : GP.gR g⁻¹ = (GP.gR g)⁻¹ := by
  simp [GP.gR, Reduction.infAt_inv, map_inv]

theorem gR_ti (g : G3) : GP.gR (ti g) = GL2LocalData.tinvR (GP.gR g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change (GP.gR (ti g)).val i j = ((GP.gR g)⁻¹ : GL (Fin 3) ℝ).val j i
  rw [← gR_inv]
  rfl

theorem real_component_weyl_GL3 : GP.gR (w3 : G3) = GL2LocalData.w3R := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [GP.gR, w3, GL2LocalData.w3R, Reduction.infAt_apply] <;> rfl

theorem gR_dual (g : G3) : GP.gR (w3 * ti g) = GL2LocalData.w3R * GL2LocalData.tinvR (GP.gR g) := by
  rw [gR_mul, real_component_weyl_GL3, gR_ti]

local notation "rP" => GroundTheory.Automorphic.GL2Classical.realPart

theorem rP_mul (g h : G2) : rP (g * h) = rP g * rP h := by
  simp [GroundTheory.Automorphic.GL2Classical.realPart, map_mul]

theorem rP_inv (g : G2) : rP g⁻¹ = (rP g)⁻¹ := by
  simp [GroundTheory.Automorphic.GL2Classical.realPart, map_inv]

theorem rP_ti (g : G2) : rP (ti g) = GL2LocalData.tinvR (rP g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change (rP (ti g)).val i j = ((rP g)⁻¹ : GL (Fin 2) ℝ).val j i
  rw [← rP_inv]
  rfl

theorem real_component_weyl_GL2 : rP (w2 : G2) = GL2LocalData.w2R := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;>
    simp [GroundTheory.Automorphic.GL2Classical.realPart, w2, GL2LocalData.w2R, AdelicGLn.prodEquiv_apply_fst] <;> rfl

theorem dual_pure (Wi : GL (Fin 3) ℝ → ℂ) (Wt : GL (Fin 2) ℝ → ℂ) (Wf : ∀ v : Pl, GL (Fin 3) (Qv v) → ℂ)
    (Wtf : ∀ v : Pl, GL (Fin 2) (Qv v) → ℂ) :
    dualWhittakerAdelicGL3 (GP.pw Wi Wf) = GP.pw (GL2LocalData.dW3R Wi) (fun v => GL2LocalData.dW3 (Wf v)) ∧
      dualWhittakerAdelic (pw2 Wt Wtf) = pw2 (GL2LocalData.dW2R Wt) (fun v => GL2LocalData.dW2 (Wtf v)) := by
  refine ⟨funext fun g => ?_, funext fun h => ?_⟩
  · have hv : ∀ v : Pl, finAt v ((w3 : G3) * ti g) = GL2LocalData.w3 * GL2LocalData.tinv (finAt v g) := fun v => by
      rw [Reduction.finAt_mul, finite_component_weyl_GL3, finAt_ti]
    simp only [dualWhittakerAdelicGL3, GP.pw, GL2LocalData.dW3R, GL2LocalData.dW3, gR_dual, hv]
  · have hv : ∀ v : Pl, finAt v ((w2 : G2) * ti h) = GL2LocalData.w2 * GL2LocalData.tinv (finAt v h) := fun v => by
      rw [Reduction.finAt_mul, finite_component_weyl_GL2, finAt_ti]
    simp only [dualWhittakerAdelic, pw2, GL2LocalData.dW2R, GL2LocalData.dW2, rP_mul, real_component_weyl_GL2, rP_ti, hv]

end GlobalTheory.CompanionTheory.GL2Factorization.Dual
