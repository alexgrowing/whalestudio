import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ThetaSquareIntegrable
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.SobSym

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem psi_real (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) :
    ∃ Λ : Ainf D.host.F →+ ℂ, Continuous Λ ∧ ∀ z : AF D.host.F, z.2 = 0 → ψ z = Complex.exp (Λ z.1) := by
  obtain ⟨⟨θ, hθ⟩, hall⟩ := hψ.2
  have hf := hall θ hθ
  let Λ : Ainf D.host.F →+ ℂ :=
    { toFun := fun y => 2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * ∑ ρ, θ ρ (y ⊗ₜ[D.host.F] (1 : D.host.E))
      map_zero' := by simp
      map_add' := fun y y' => by simp only [TensorProduct.add_tmul, map_add, Finset.sum_add_distrib]; ring }
  refine ⟨Λ, ?_, fun z hz => ?_⟩
  · show Continuous fun y => 2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * ∑ ρ, θ ρ (y ⊗ₜ[D.host.F] (1 : D.host.E))
    exact continuous_const.mul (continuous_finset_sum _ fun ρ _ => (hθ ρ).2)
  · have hz' : z = pairA D.host.F z.1 0 := Prod.ext rfl hz
    rw [hz']
    exact hf z.1

theorem norm_iter_exp {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (ℓ : V →L[ℝ] ℂ) :
    ∀ (i : ℕ) (u : V), ‖iteratedFDeriv ℝ i (fun v => Complex.exp (ℓ v)) u‖ ≤ ‖Complex.exp (ℓ u)‖ * ‖ℓ‖ ^ i := by
  have hp : ContDiff ℝ ∞ (fun v => Complex.exp (ℓ v)) :=
    (Complex.contDiff_exp (𝕜 := ℝ)).comp ℓ.contDiff
  intro i
  induction i with
  | zero => intro u; simp [norm_iteratedFDeriv_zero]
  | succ i ih =>
    intro u
    rw [← norm_iteratedFDeriv_fderiv]
    let T : ℂ →L[ℝ] (V →L[ℝ] ℂ) := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℂ) ℓ
    have hT : ∀ a : ℂ, T a = a • ℓ := fun a => rfl
    have hfd : fderiv ℝ (fun v => Complex.exp (ℓ v)) = T ∘ (fun v => Complex.exp (ℓ v)) := by
      funext v
      rw [Function.comp_apply, hT, ((ℓ.hasFDerivAt (x := v)).cexp).fderiv]
    rw [hfd]
    refine (T.norm_iteratedFDeriv_comp_left hp.contDiffAt (natCast_lt_inf' i).le).trans ?_
    have hTn : ‖T‖ ≤ ‖ℓ‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun a => ?_
      rw [hT, norm_smul, mul_comm]
    calc ‖T‖ * ‖iteratedFDeriv ℝ i (fun v => Complex.exp (ℓ v)) u‖
        ≤ ‖ℓ‖ * (‖Complex.exp (ℓ u)‖ * ‖ℓ‖ ^ i) :=
          mul_le_mul hTn (ih u) (norm_nonneg _) (norm_nonneg _)
      _ = ‖Complex.exp (ℓ u)‖ * ‖ℓ‖ ^ (i + 1) := by ring

end Formalism.IndefR.Eqv

end
