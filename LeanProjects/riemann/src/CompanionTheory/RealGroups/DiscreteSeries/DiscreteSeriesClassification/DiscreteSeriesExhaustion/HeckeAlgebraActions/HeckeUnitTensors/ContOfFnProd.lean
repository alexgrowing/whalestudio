import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantTensor
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeRankOneStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.OmegaMinorStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PrincipalSumStatement
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

noncomputable section

open Finset

namespace CompanionTheory.RgExh.Hk.UnitPf

open Formalism.REAL (qdet qminor Tm GlRel)
open CompanionTheory.RgExh

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

private theorem continuous_apply_list_prod_ofFn_add_smul : ∀ (m : ℕ) (ℓ : Module.Dual ℂ W) (A B : Fin m → Module.End ℂ W) (f : W),
    Continuous (fun u : ℂ => ℓ ((List.ofFn fun k => A k + u • B k).prod f)) := by
  intro m
  induction m with
  | zero =>
    intro ℓ A B f
    simp only [List.ofFn_zero, List.prod_nil]
    exact continuous_const
  | succ m ih =>
    intro ℓ A B f
    have h : (fun u : ℂ => ℓ ((List.ofFn fun k => A k + u • B k).prod f)) =
        fun u : ℂ => (ℓ ∘ₗ A 0) ((List.ofFn fun k : Fin m => A k.succ + u • B k.succ).prod f) +
          u * (ℓ ∘ₗ B 0) ((List.ofFn fun k : Fin m => A k.succ + u • B k.succ).prod f) := by
      funext u
      simp only [List.ofFn_succ, List.prod_cons, Module.End.mul_apply, LinearMap.add_apply,
        LinearMap.smul_apply, map_add, map_smul, smul_eq_mul, LinearMap.comp_apply]
    rw [h]
    exact (ih (ℓ ∘ₗ A 0) (fun k => A k.succ) (fun k => B k.succ) f).add
      (continuous_id.mul (ih (ℓ ∘ₗ B 0) (fun k => A k.succ) (fun k => B k.succ) f))

theorem cont_ofFn_prod (ℓ : Module.Dual ℂ W) : ∀ (m : ℕ) (A B : Fin m → Module.End ℂ W) (f : W),
    Continuous (fun u : ℂ => ℓ ((List.ofFn fun k => A k + u • B k).prod f)) := by
  intro m A B f
  exact continuous_apply_list_prod_ofFn_add_smul m ℓ A B f

theorem Tm_affine {n : ℕ} (E : Fin n → Fin n → Module.End ℂ W) (u : ℂ) (k : ℂ) (a b : Fin n) :
    Tm E (u - k) a b = ((if a = b then algebraMap ℂ (Module.End ℂ W) (-k) else 0) + E a b) +
      u • (if a = b then (1 : Module.End ℂ W) else 0) := by
  unfold Tm
  split_ifs with h
  · rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, sub_eq_add_neg, add_smul]
    abel
  · simp

theorem cont_qdet {n : ℕ} (E : Fin n → Fin n → Module.End ℂ W) (ℓ : Module.Dual ℂ W) (f : W) :
    Continuous (fun u : ℂ => ℓ (qdet E u f)) := by
  simp only [qdet, qminor, LinearMap.sum_apply, map_sum]
  refine continuous_finsetSum _ fun σ _ => ?_
  simp only [Module.End.mul_apply, Module.End.intCast_apply, map_zsmul, Tm_affine]
  exact (cont_ofFn_prod ℓ n _ _ f).const_smul _

theorem eq_zero_of_off {g : ℂ → ℂ} (hg : Continuous g) (u₀ : ℂ) (h : ∀ u, u ≠ u₀ → g u = 0) : g u₀ = 0 := by
  have hd : Dense ({u₀}ᶜ : Set ℂ) := dense_compl_singleton u₀
  have h0 : g = fun _ => 0 :=
    hg.ext_on hd (continuous_const : Continuous fun _ : ℂ => (0 : ℂ)) (fun u hu => h u hu)
  exact congrFun h0 u₀

end CompanionTheory.RgExh.Hk.UnitPf
