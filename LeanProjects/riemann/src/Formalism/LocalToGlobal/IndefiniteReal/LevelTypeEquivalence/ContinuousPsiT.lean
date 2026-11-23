import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.FatouOm
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct ContDiff ENNReal

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ}

theorem dH_comp_bound {ψ : AddChar (AF D.host.F) ℂ} {f : WO S T → ℂ} {L M : (Fin k → ℝ) →+ WO S T}
    (A : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ)) (hMA : ∀ t, M t = L (A t)) (x : WO S T)
    (hs : ContDiff ℝ ∞ (Gf ψ L f x)) {n : ℕ} (l : Fin n → Fin k) :
    ‖dH ψ M l f x‖ ≤ ‖A‖ ^ n * ∑ l' : Fin n → Fin k, ‖dH ψ L l' f x‖ := by
  unfold dH
  have hs' : ContDiff ℝ ∞ (fun t => heisO ψ S T (L t) f x) := hs
  have hcomp : (fun t => heisO ψ S T (M t) f x) = (fun t => heisO ψ S T (L t) f x) ∘ A := by
    funext t
    simp only [Function.comp_apply, hMA]
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right A hs' 0
      (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)),
    ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]
  set Dg := iteratedFDeriv ℝ n (fun t => heisO ψ S T (L t) f x) 0 with hDg
  have hexp : ∀ v : Fin k → ℝ, v = ∑ j, v j • Pi.single j (1 : ℝ) := fun v => by
    ext m
    simp [Finset.sum_apply, Pi.single_apply]
  have he1 : ∀ j : Fin k, ‖(Pi.single j (1 : ℝ) : Fin k → ℝ)‖ ≤ 1 := fun j => by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun m => ?_
    by_cases h : m = j
    · subst h
      simp
    · simp [Pi.single_apply, h]
  have hc : ∀ i j, ‖(A (Pi.single (l i) (1 : ℝ))) j‖ ≤ ‖A‖ := fun i j =>
    (norm_le_pi_norm _ j).trans ((A.le_opNorm _).trans
      (by simpa using mul_le_mul_of_nonneg_left (he1 (l i)) (norm_nonneg A)))
  rw [show (fun i => A (Pi.single (l i) (1 : ℝ))) =
      fun i => ∑ j, (A (Pi.single (l i) (1 : ℝ))) j • Pi.single j (1 : ℝ) from funext fun i => hexp _,
    ContinuousMultilinearMap.map_sum]
  simp only [ContinuousMultilinearMap.map_smul_univ]
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [norm_smul, norm_prod]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  calc ∏ i, ‖(A (Pi.single (l i) (1 : ℝ))) (r i)‖ ≤ ∏ _i : Fin n, ‖A‖ :=
        Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => hc i (r i)
    _ = ‖A‖ ^ n := by simp

theorem continuous_psiT (τ : D.what₂.Tau) : Continuous (psiT D τ) := by
  have heq : (psiT D τ : AE D → ℂ) = fun x => gW D (plW D τ) (fstA D.host.F ((basAF D).repr x 0)) +
      gW D (plW D τ) (fstA D.host.F ((basAF D).repr x 1)) * betaT D τ := by
    funext x
    simp only [psiT, RingHom.coe_comp, Function.comp_apply]
    rw [thetaC_decomp, repr_infPart, repr_infPart]
  rw [heq]
  have hc : ∀ k : Fin 2, Continuous fun x : AE D => (basAF D).repr x k := fun k => by
    have := (continuous_apply k).comp (G5.tensCoordH (basE D) (AF D.host.F)).continuous
    convert this using 1
    funext x
    simp only [Function.comp_apply, G5.tensCoordH_apply]
    rfl
  have hf : Continuous (fstA D.host.F) := continuous_fst
  exact ((continuous_gW (D := D) _).comp (hf.comp (hc 0))).add
    (((continuous_gW (D := D) _).comp (hf.comp (hc 1))).mul continuous_const)

end Formalism.IndefR.Eqv

end
