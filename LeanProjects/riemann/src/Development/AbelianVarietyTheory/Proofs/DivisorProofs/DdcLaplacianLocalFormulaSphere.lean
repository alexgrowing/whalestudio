import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppendVMemFamAtlasTarget
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcEqOfLocalEq

set_option autoImplicit false

open Set MeasureTheory Filter
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm GlobalTheory.BcUnique GlobalTheory.HermFrame
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff Real Topology

namespace GlobalTheory.BcUnique

theorem loc_ddc_fn {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) (g : M → ℝ) (i : A.ι) {x : V n}
    (hx : x ∈ (A.e i).target) {u : V n → ℝ} (hu : ContDiffAt ℝ 2 u x) (h : ∀ v, g ((A.e i).symm v) = u v) :
    A.loc (A.ddc (A.fn g)) i x = ofValues (ddc u x) := by
  rw [HolAtlas.loc, dif_pos hx, ← delAt_dbarAt_fun hu]
  have e : (A.e i) ((A.e i).symm x) = x := (A.e i).right_inv hx
  refine (GlobalTheory.SecForm.DdcGerm.ddc_eq_of_eventuallyEq A _ _ (fun x => algebraMap ℂ (Alt n) (u x)) ?_).trans ?_
  · change A.loc (A.fn g) i =ᶠ[𝓝 ((A.e i) ((A.e i).symm x))] _
    rw [e]
    filter_upwards [(A.e i).open_target.mem_nhds hx] with w hw
    rw [HolAtlas.loc, dif_pos hw, ← h w]
    rfl
  · change kappa • delAt _ ((A.e i) ((A.e i).symm x)) = _
    rw [e]

theorem leviForm_coord {n : ℕ} (c : Fin n) {φ : ℂ → ℝ} {x : V n} (hφ : ContDiffAt ℝ 2 φ (x c)) (v w : V n) :
    leviForm (fun y : V n => φ (y c)) x v w = v c * (starRingEnd ℂ) (w c) * ((Laplacian.laplacian φ (x c) / 4 : ℝ) : ℂ) := by
  let L : V n →L[ℂ] ℂ := EuclideanSpace.proj c
  have := leviForm_comp_holo (u := φ) (φ := L) (z := x) hφ L.contDiff.contDiffAt v w
  rw [L.fderiv] at this
  refine this.trans ?_
  rw [← leviForm_one_one_eq_laplacian hφ]
  have h1 : L v = v c • (1 : ℂ) := by simp [L]
  have h2 : L w = w c • (1 : ℂ) := by simp [L]
  rw [h1, h2, map_smulₛₗ, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm,
    mul_assoc]
  rfl

theorem loc_ddc_snd : ∀ (M : Type) [TopologicalSpace M] (A : HolAtlas M 1) (φ : ℂ → ℝ), ContDiff ℝ ∞ φ → ∀ (j : A.ι) (x : V (1 + 1)), x ∈ ((famAtlas A).e (j, sphFin)).target → (famAtlas A).loc ((famAtlas A).ddc ((famAtlas A).fn fun y => y.2.elim 0 φ)) (j, sphFin) x = ((Laplacian.laplacian φ (x (Fin.last 1)) / (4 * π) : ℝ) : ℂ) • ((Complex.I / 2) • (dz (Fin.last 1) * dzb (Fin.last 1))) := by
  intro M _ A φ hφ j x hx
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_cast)
  have hu : ContDiffAt ℝ 2 (fun y : V (1 + 1) => φ (y (Fin.last 1))) x :=
    (h2.comp ((EuclideanSpace.proj (Fin.last 1) : V (1 + 1) →L[ℂ] ℂ).restrictScalars ℝ).contDiff).contDiffAt
  rw [loc_ddc_fn (famAtlas A) _ (j, sphFin) hx hu fun v => rfl]
  simp only [ofValues, ddc, leviForm_coord (Fin.last 1) h2.contDiffAt, AddSubmonoidClass.coe_finset_sum,
    Subalgebra.coe_smul, sym, smul_smul]
  have hc (a : Fin (1 + 1)) (ha : a ≠ Fin.last 1) : coordVec a (Fin.last 1) = (0 : ℂ) := by
    have h : (1 : Fin (1 + 1)) ≠ a := ha.symm
    simp [coordVec, h]
  rw [Finset.sum_eq_single (Fin.last 1) (fun a _ ha => by
    simp only [hc a ha, zero_mul, mul_zero, map_zero, zero_smul, Finset.sum_const_zero]) (by simp),
    Finset.sum_eq_single (Fin.last 1) (fun a _ ha => by
    simp only [hc a ha, zero_mul, mul_zero, map_zero, zero_smul, Finset.sum_const_zero]) (by simp)]
  congr 1
  have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [coordVec, kappa, EuclideanSpace.single_apply, if_true, map_one]
  push_cast
  field_simp

end GlobalTheory.BcUnique
