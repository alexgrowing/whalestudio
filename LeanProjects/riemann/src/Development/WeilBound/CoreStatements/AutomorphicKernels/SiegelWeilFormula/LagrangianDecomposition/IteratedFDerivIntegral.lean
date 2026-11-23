import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzVanishingDecomposition

noncomputable section

open scoped ContDiff
open MeasureTheory Set Filter Topology

namespace PositivityTheory.SiegelWeilFormula.Ald.PCI

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def pder (n : ℕ) (Θ : V × ℝ → ℂ) (p : V × ℝ) : ContinuousMultilinearMap ℝ (fun _ : Fin n => V) ℂ :=
  iteratedFDeriv ℝ n (fun y => Θ (y, p.2)) p.1

theorem pder_eq (n : ℕ) {Θ : V × ℝ → ℂ} (hΘ : ContDiff ℝ ∞ Θ) (p : V × ℝ) :
    pder n Θ p = (iteratedFDeriv ℝ n Θ p).compContinuousLinearMap (fun _ => ContinuousLinearMap.inl ℝ V ℝ) := by
  have e : (fun y => Θ (y, p.2)) = (fun z => Θ (z + (0, p.2))) ∘ ContinuousLinearMap.inl ℝ V ℝ := by
    funext y; simp
  have hg : ContDiff ℝ ∞ (fun z => Θ (z + (0, p.2))) := hΘ.comp (contDiff_id.add contDiff_const)
  rw [pder, e, ContinuousLinearMap.iteratedFDeriv_comp_right _ hg _ (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_right]
  simp

theorem contDiff_pder (n : ℕ) {Θ : V × ℝ → ℂ} (hΘ : ContDiff ℝ ∞ Θ) : ContDiff ℝ ∞ (pder n Θ) := by
  have : pder n Θ = (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin n => ContinuousLinearMap.inl ℝ V ℝ)) ∘ iteratedFDeriv ℝ n Θ := by
    funext p; rw [pder_eq n hΘ p]; rfl
  rw [this]
  exact (ContinuousLinearMap.contDiff _).comp (hΘ.iteratedFDeriv_right (by norm_cast))

variable [FiniteDimensional ℝ V]

theorem iteratedFDeriv_integral {Θ : V × ℝ → ℂ} (hΘ : ContDiff ℝ ∞ Θ) (n : ℕ) (x : V) :
    iteratedFDeriv ℝ n (fun y => ∫ s in Ioc (0 : ℝ) 1, Θ (y, s)) x = ∫ s in Ioc (0 : ℝ) 1, pder n Θ (x, s) := by
  induction n generalizing x with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    simp only [Function.comp_apply, pder, iteratedFDeriv_zero_eq_comp]
    exact ((continuousMultilinearCurryFin0 ℝ V ℂ).symm.toLinearIsometry.integral_comp_comm _).symm
  | succ n ih =>
    have hfun : iteratedFDeriv ℝ n (fun y => ∫ s in Ioc (0 : ℝ) 1, Θ (y, s)) =
        fun y => ∫ s in Ioc (0 : ℝ) 1, (1 : ℂ) • pder n Θ (y, id s) := by
      funext y; simp [ih y]
    have hd := GlobalTheory.SchwartzDiv.hasFDerivAt_integral_smul_param (ν := volume.restrict (Ioc (0 : ℝ) 1)) (c := id)
      (S := Icc (0 : ℝ) 1) (φ := fun _ => (1 : ℂ)) aestronglyMeasurable_id isCompact_Icc
      ((ae_restrict_mem measurableSet_Ioc).mono fun t ht => Ioc_subset_Icc_self ht)
      (integrableOn_const (by simp)) (contDiff_pder n hΘ) x
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hfun, hd.fderiv]
    have hc := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => V) ℂ).symm.toLinearIsometry.integral_comp_comm
      (μ := volume.restrict (Ioc (0 : ℝ) 1)) (fun y => (1 : ℂ) • fderiv ℝ (fun s => pder n Θ (s, id y)) x)
    simp only [LinearIsometryEquiv.coe_toLinearIsometry] at hc
    rw [← hc]
    refine integral_congr_ae (.of_forall fun s => ?_)
    simp only [one_smul, id, pder]
    rw [iteratedFDeriv_succ_eq_comp_left]
    rfl

end PositivityTheory.SiegelWeilFormula.Ald.PCI

end
