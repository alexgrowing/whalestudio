import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsEventuallyNormRiemannThetaTermLe
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.LineDerivListEqIteratedFDeriv

open Complex Matrix Filter Topology
open scoped Real

noncomputable section

namespace GlobalTheory

variable {ι : Type*} [Fintype ι]

def riemannThetaJointForm (a : ι → ℝ) (n : ι → ℤ) : ((ι → ℂ) × (ι → ι → ℂ)) →L[ℂ] ℂ :=
  (riemannThetaForm a n).coprod (∑ i, ∑ j, (π * I * (((n i : ℂ) + a i) * ((n j : ℂ) + a j))) •
    (ContinuousLinearMap.proj j : (ι → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ι → ℂ) i))

@[simp] theorem riemannThetaJointForm_apply (a : ι → ℝ) (n : ι → ℤ)
    (p : (ι → ℂ) × (ι → ι → ℂ)) :
    riemannThetaJointForm a n p =
      2 * π * I * (((fun i => (n i : ℂ) + a i) ⬝ᵥ (of p.2 *ᵥ fun i => (n i : ℂ) + a i)) / 2 +
        (fun i => (n i : ℂ) + a i) ⬝ᵥ p.1) := by
  obtain ⟨w, A⟩ := p
  have : ∑ i, ∑ j, π * I * (((n i : ℂ) + a i) * ((n j : ℂ) + a j)) * A i j =
      π * I * ((fun i => (n i : ℂ) + a i) ⬝ᵥ (of A *ᵥ fun i => (n i : ℂ) + a i)) := by
    simp only [dotProduct, mulVec, Finset.mul_sum, of_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [riemannThetaJointForm, ContinuousLinearMap.coprod_apply, riemannThetaForm_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, this]
  ring

theorem riemannThetaTerm_eq_cexp_jointForm (a b : ι → ℝ) (n : ι → ℤ)
    (p : (ι → ℂ) × (ι → ι → ℂ)) :
    riemannThetaTerm a b (of p.2) p.1 n =
      cexp (riemannThetaJointForm a n p + riemannThetaForm a n fun i => (b i : ℂ)) := by
  have : (fun i => p.1 i + (b i : ℂ)) = p.1 + fun i => (b i : ℂ) := rfl
  rw [riemannThetaTerm, riemannThetaJointForm_apply, riemannThetaForm_apply, this, dotProduct_add]
  congr 1
  ring

theorem differentiable_riemannThetaTerm (a b : ι → ℝ) (n : ι → ℤ) :
    Differentiable ℂ fun p : (ι → ℂ) × (ι → ι → ℂ) => riemannThetaTerm a b (of p.2) p.1 n := by
  simp only [riemannThetaTerm_eq_cexp_jointForm]
  fun_prop

theorem IsSiegel.exists_isOpen_norm_riemannThetaTerm_le {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω)
    (a b : ι → ℝ) (v : ι → ℂ) : ∃ U : Set ((ι → ℂ) × (ι → ι → ℂ)), IsOpen U ∧ (v, of.symm Ω) ∈ U ∧
      ∃ u : (ι → ℤ) → ℝ, Summable u ∧
        ∀ n, ∀ p ∈ U, ‖riemannThetaTerm a b (of p.2) p.1 n‖ ≤ u n := by
  obtain ⟨c, hc, S, hS⟩ := h.exists_eventually_norm_riemannThetaTerm_le a b v
  obtain ⟨U, hU, hUo, hp⟩ := _root_.eventually_nhds_iff.mp hS
  exact ⟨U, hUo, hp, _, summable_riemannThetaBound a hc S, fun n p hp => hU p hp n⟩

theorem IsSiegel.analyticAt_riemannTheta_entries {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω)
    (a b : ι → ℝ) (v : ι → ℂ) :
    AnalyticAt ℂ (fun p : (ι → ℂ) × (ι → ι → ℂ) => riemannTheta a b (of p.2) p.1)
      (v, of.symm Ω) := by
  obtain ⟨U, hU, hp, u, hu, hle⟩ := h.exists_isOpen_norm_riemannThetaTerm_le a b v
  exact SCV.analyticAt_of_differentiableOn (SCV.differentiableOn_tsum_of_locally_normal hU
    (fun n => (differentiable_riemannThetaTerm a b n).differentiableOn)
    fun x hx => ⟨U, hU.mem_nhds hx, u, hu, hle⟩) (hU.mem_nhds hp)

section Families

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem differentiableOn_riemannTheta_comp (a b : ι → ℝ) {Ω : E → Matrix ι ι ℂ} {v : E → ι → ℂ}
    {U : Set E} (h : ∀ x ∈ U, IsSiegel (Ω x)) (hΩ : ∀ i j, DifferentiableOn ℂ (fun y => Ω y i j) U)
    (hv : DifferentiableOn ℂ v U) :
    DifferentiableOn ℂ (fun y => riemannTheta a b (Ω y) (v y)) U := fun x hx =>
  ((h x hx).analyticAt_riemannTheta_entries a b (v x)).differentiableAt.comp_differentiableWithinAt
    (f := fun y => (v y, of.symm (Ω y))) x
    ((hv x hx).prodMk
      (differentiableWithinAt_pi.mpr fun i => differentiableWithinAt_pi.mpr fun j => hΩ i j x hx))

end Families

def symmSingle {ι : Type*} [DecidableEq ι] (i j : ι) : Matrix ι ι ℂ :=
  of fun k l => if k = i ∧ l = j ∨ k = j ∧ l = i then 1 else 0

section Upper

variable {ι : Type*} [LinearOrder ι]

def symmOfUpper (x : {p : ι × ι // p.1 ≤ p.2} → ℂ) : Matrix ι ι ℂ :=
  of fun i j => x ⟨(min i j, max i j), min_le_max⟩

def siegelUpperCoords (ι : Type*) [LinearOrder ι] : Set ({p : ι × ι // p.1 ≤ p.2} → ℂ) :=
  symmOfUpper ⁻¹' siegelUpperHalfSpace ι

@[simp] theorem mem_siegelUpperCoords {x : {p : ι × ι // p.1 ≤ p.2} → ℂ} :
    x ∈ siegelUpperCoords ι ↔ IsSiegel (symmOfUpper x) := Iff.rfl

variable [Fintype ι]

end Upper

end GlobalTheory
