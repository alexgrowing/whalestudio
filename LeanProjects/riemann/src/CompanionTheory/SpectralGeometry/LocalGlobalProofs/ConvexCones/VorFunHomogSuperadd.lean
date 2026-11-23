import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarisationBaseFunctionProperties

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem evalR_vorFun_eq (O : Type) [CommRing O] [Module.Finite ℤ O] (g : ℕ) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] [Module.Finite ℤ X] {d : ℕ} {s : (Fin d → ℤ) →ₗ[ℤ] X} (hs : Function.Surjective s)
    (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    evalR (vorFun O g) B = (fineDen g {1} : ℝ) *
      ((((1 : ℕ) : ℝ) + 1) ^ d)⁻¹ * ∑ y, classMin 1 (fun a b => B (s a) (s b)) y := by
  have h0 : zeroFun.eval X (fun a b => B a b) = 0 := by
    rw [zeroFun.eval_eq hs]
    rfl
  rw [evalR, vorFun, eval_baseFun, h0, Finset.sum_singleton, fineMean_eval_eq 1 hs, zero_add, mul_assoc]

theorem vorFun_homog_superadd : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (g : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X],
    (∀ B ∈ psdCone bar X, ∀ t : ℝ, 0 ≤ t → evalR (vorFun O g) (t • B) = t * evalR (vorFun O g) B) ∧
    ∀ B ∈ psdCone bar X, ∀ B' ∈ psdCone bar X,
      evalR (vorFun O g) B + evalR (vorFun O g) B' ≤ evalR (vorFun O g) (B + B') := by
  intro O _ _ _ _ bar g X _ _ _
  have : Module.Finite ℤ X := Module.Finite.trans O X
  obtain ⟨d, s, hs⟩ := Module.Finite.exists_fin' ℤ X
  have hc : (0 : ℝ) ≤ (fineDen g {1} : ℝ) * ((((1 : ℕ) : ℝ) + 1) ^ d)⁻¹ := by positivity
  refine ⟨fun B _ t ht => ?_, fun B hB B' hB' => ?_⟩
  · rw [evalR_vorFun_eq O g hs, evalR_vorFun_eq O g hs]
    simp only [LinearMap.smul_apply, smul_eq_mul, classMin_smul ht, ← Finset.mul_sum]
    ring
  · rw [evalR_vorFun_eq O g hs, evalR_vorFun_eq O g hs, evalR_vorFun_eq O g hs, ← mul_add,
      ← Finset.sum_add_distrib]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => ?_) hc
    simp only [LinearMap.add_apply]
    exact classMin_add_le (fun a => nonneg_of_mem_psdCone hB _) (fun a => nonneg_of_mem_psdCone hB' _) y

end GlobalTheory.CompanionTheory.Ar.Fan
