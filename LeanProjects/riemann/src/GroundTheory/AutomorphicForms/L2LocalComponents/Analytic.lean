import Mathlib
import GroundTheory.AutomorphicForms.HarishChandraRegularity
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.Density

namespace GroundTheory.Automorphic

open Filter Topology Polynomial
open scoped ContDiff InnerProductSpace

set_option linter.unusedSectionVars false

namespace IsExpLieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E)

theorem isSmoothFun_coeff {v : E} (hv : h.IsSmoothVector π v) (ℓ : E →L[ℂ] ℂ) :
    h.IsSmoothFun (fun g : G => ℓ (π g v)) := by
  let _ := h.chartedSpace
  exact (ℓ.restrictScalars ℝ).contDiff.comp_contMDiff hv

theorem rightDeriv_coeff {v : E} (hv : h.IsSmoothVector π v) (ℓ : E →L[ℂ] ℂ) (X : 𝔤) :
    h.rightDeriv X (fun g : G => ℓ (π g v)) = fun g => ℓ (π g (h.derivOp π X v)) := by
  funext g
  have e : (fun Y : 𝔤 => ℓ (π (g * h.expG Y) v)) =
      ((ℓ.comp (π g)).restrictScalars ℝ) ∘ h.expOrbit π v := by
    funext Y
    simp [expOrbit]
  have hd : HasFDerivAt (fun Y : 𝔤 => ℓ (π (g * h.expG Y) v))
      (((ℓ.comp (π g)).restrictScalars ℝ).comp (fderiv ℝ (h.expOrbit π v) 0)) 0 := by
    rw [e]
    exact ((ℓ.comp (π g)).restrictScalars ℝ).hasFDerivAt.comp 0
      ((h.differentiable_expOrbit π hv 0).hasFDerivAt)
  show fderiv ℝ (fun Y : 𝔤 => ℓ (π (g * h.expG Y) v)) 0 X = _
  rw [hd.fderiv]
  rfl

noncomputable def coeffFun (ℓ : E →L[ℂ] ℂ) (v : h.smoothVectors π) : h.smoothFuns (F := ℂ) :=
  ⟨fun g => ℓ (π g v), h.isSmoothFun_coeff π v.2 ℓ⟩

@[simp] theorem coe_coeffFun (ℓ : E →L[ℂ] ℂ) (v : h.smoothVectors π) :
    ((h.coeffFun π ℓ v : h.smoothFuns (F := ℂ)) : G → ℂ) = fun g => ℓ (π g v) := rfl

noncomputable def coeffLin (ℓ : E →L[ℂ] ℂ) : h.smoothVectors π →ₗ[ℂ] h.smoothFuns (F := ℂ) where
  toFun := h.coeffFun π ℓ
  map_add' v w := Subtype.ext (funext fun g => by simp)
  map_smul' c v := Subtype.ext (funext fun g => by simp)

@[simp] theorem coeffLin_apply (ℓ : E →L[ℂ] ℂ) (v : h.smoothVectors π) :
    h.coeffLin π ℓ v = h.coeffFun π ℓ v := rfl

theorem rightUAction_coeffFun (ℓ : E →L[ℂ] ℂ) (u : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra)
    (v : h.smoothVectors π) :
    h.rightUAction (F := ℂ) u (h.coeffFun π ℓ v) = h.coeffFun π ℓ (h.uAction π u v) := by
  obtain ⟨t, rfl⟩ : ∃ t, UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra t = u :=
    RingCon.mkₐ_surjective (α := ℝ) (UniversalEnvelopingAlgebra.ringCon ℝ h.lieSubalgebra) u
  induction t using TensorAlgebra.induction generalizing v with
  | algebraMap r =>
    simp only [AlgHom.commutes, Module.algebraMap_end_apply]
    apply Subtype.ext
    funext g
    simp only [coe_coeffFun]
    show r • ℓ (π g v) = ℓ (π g ((r • v : h.smoothVectors π) : E))
    rw [Submodule.coe_smul_of_tower, ← Complex.coe_smul, ← Complex.coe_smul, map_smul, map_smul]
  | ι x =>
    show h.rightUAction (F := ℂ) (UniversalEnvelopingAlgebra.ι ℝ x) (h.coeffFun π ℓ v) =
      h.coeffFun π ℓ (h.uAction π (UniversalEnvelopingAlgebra.ι ℝ x) v)
    rw [rightUAction_ι, uAction_ι]
    apply Subtype.ext
    rw [coe_rightDerivEnd, coe_coeffFun, rightDeriv_coeff h π v.2]
    rfl
  | mul a b iha ihb =>
    rw [map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ihb, iha]
  | add a b iha ihb =>
    rw [map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, iha, ihb]
    exact ((h.coeffLin π ℓ).map_add _ _).symm

noncomputable def laplacianElt {ι : Type*} [Fintype ι] (bL : Module.Basis ι ℝ h.lieSubalgebra) :
    UniversalEnvelopingAlgebra ℝ h.lieSubalgebra :=
  ∑ i, UniversalEnvelopingAlgebra.ι ℝ (bL i) * UniversalEnvelopingAlgebra.ι ℝ (bL i)

theorem rightUAction_laplacianElt {ι : Type*} [Fintype ι] (bL : Module.Basis ι ℝ h.lieSubalgebra) :
    h.rightUAction (F := ℂ) (h.laplacianElt bL) = h.laplacian bL := by
  simp only [laplacianElt, laplacian, map_sum, map_mul, rightUAction_ι]

theorem comp_aeval_eq {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (Φ : V →ₗ[ℂ] W) {A : Module.End ℂ V} {B : Module.End ℂ W} (hAB : Φ ∘ₗ A = B ∘ₗ Φ) (P : ℂ[X]) :
    Φ ∘ₗ (aeval A P) = (aeval B P) ∘ₗ Φ := by
  have hpow : ∀ k : ℕ, Φ ∘ₗ (A ^ k) = (B ^ k) ∘ₗ Φ := by
    intro k
    induction k with
    | zero => simp [Module.End.one_eq_id]
    | succ k ih =>
      rw [pow_succ, pow_succ, Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← LinearMap.comp_assoc,
        ih, LinearMap.comp_assoc, hAB, LinearMap.comp_assoc]
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, LinearMap.comp_add, LinearMap.add_comp, hp, hq]
  | monomial k c =>
    rw [aeval_monomial, aeval_monomial]
    ext v
    simp only [LinearMap.comp_apply, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]
    rw [← LinearMap.comp_apply Φ (A ^ k), hpow]
    rfl

theorem analyticAt_coeff {ι : Type*} [Fintype ι] (bL : Module.Basis ι ℝ h.lieSubalgebra) {P : ℂ[X]}
    (hP : P.Monic) {v : h.smoothVectors π} (hv : aeval (h.uAction π (h.laplacianElt bL)) P v = 0)
    (ℓ : E →L[ℂ] ℂ) (g : G) : AnalyticAt ℝ (fun Y : 𝔤 => ℓ (π (g * h.expG Y) v)) 0 := by
  refine h.analyticAt_of_aeval_laplacian_eq_zero bL P hP (h.coeffFun π ℓ v) ?_ g
  have hc : h.coeffLin π ℓ ∘ₗ h.uAction π (h.laplacianElt bL) =
      h.laplacian bL ∘ₗ h.coeffLin π ℓ := by
    ext1 w
    simp only [LinearMap.comp_apply, coeffLin_apply]
    rw [← rightUAction_laplacianElt, rightUAction_coeffFun]
  have := congrArg (fun L => L v) (comp_aeval_eq (h.coeffLin π ℓ) hc P)
  simp only [LinearMap.comp_apply, coeffLin_apply] at this
  rw [← this, hv]
  exact (h.coeffLin π ℓ).map_zero

theorem eq_zero_of_iteratedDeriv_eq_zero {f : ℝ → ℂ} (hf : AnalyticOnNhd ℝ f Set.univ)
    (h0 : ∀ k : ℕ, iteratedDeriv k f 0 = 0) (t : ℝ) : f t = 0 := by
  have htop : analyticOrderAt f 0 = ⊤ := by
    refine ENat.eq_top_iff_forall_ge.2 fun k => ?_
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf 0 (Set.mem_univ _))).2
      fun i _ => h0 i
  have hev : f =ᶠ[𝓝 0] 0 := analyticOrderAt_eq_top.1 htop
  exact hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0) hev
    (Set.mem_univ t)

section Complete

variable [CompleteSpace E]

theorem isSmoothVector_iterate_derivOp {v : E} (hv : h.IsSmoothVector π v) (Y : 𝔤) (k : ℕ) :
    h.IsSmoothVector π ((h.derivOp π Y)^[k] v) := by
  induction k with
  | zero => exact hv
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact h.isSmoothVector_derivOp π ih Y

theorem iteratedDeriv_coeff_line {v : E} (hv : h.IsSmoothVector π v) (ℓ : E →L[ℂ] ℂ) (Y : 𝔤)
    (k : ℕ) :
    iteratedDeriv k (fun t : ℝ => ℓ (π (h.expG (t • Y)) v)) =
      fun t => ℓ (π (h.expG (t • Y)) ((h.derivOp π Y)^[k] v)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have hd := ((ℓ.restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt t
      (h.hasDerivAt_orbit_smul π (h.isSmoothVector_iterate_derivOp π hv Y k) Y t)
    rw [Function.iterate_succ_apply']
    exact hd.deriv

end Complete

end IsExpLieAlgebra

namespace IsExpLieAlgebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (π : BanachRep G E)

theorem inner_map_expG_eq_zero {ι : Type*} [Fintype ι] (bL : Module.Basis ι ℝ h.lieSubalgebra)
    (S : Submodule ℂ E) (hS : ∀ v ∈ S, h.IsSmoothVector π v)
    (hSd : ∀ X : 𝔤, ∀ v ∈ S, h.derivOp π X v ∈ S)
    (hSP : ∀ v (hv : v ∈ S), ∃ P : ℂ[X], P.Monic ∧
      aeval (h.uAction π (h.laplacianElt bL)) P ⟨v, hS v hv⟩ = 0)
    {w : E} (hw : ∀ v ∈ S, ⟪w, v⟫_ℂ = 0) {v : E} (hv : v ∈ S) (Y : 𝔤) :
    ⟪w, π (h.expG Y) v⟫_ℂ = 0 := by
  set ℓ : E →L[ℂ] ℂ := innerSL ℂ w
  have hℓ : ∀ x, ℓ x = ⟪w, x⟫_ℂ := fun x => rfl
  obtain ⟨P, hP, hPv⟩ := hSP v hv
  set f : ℝ → ℂ := fun t => ℓ (π (h.expG (t • Y)) v) with hf

  have han : AnalyticOnNhd ℝ f Set.univ := by
    intro t₀ _
    have h1 := h.analyticAt_coeff π bL hP hPv ℓ (h.expG (t₀ • Y))
    have h2 : AnalyticAt ℝ (fun t : ℝ => (t - t₀) • Y) t₀ :=
      (analyticAt_id.sub analyticAt_const).smul analyticAt_const
    have h3 : AnalyticAt ℝ ((fun Z : 𝔤 => ℓ (π (h.expG (t₀ • Y) * h.expG Z) v)) ∘
        (fun t : ℝ => (t - t₀) • Y)) t₀ := by
      refine AnalyticAt.comp ?_ h2
      simpa using h1
    refine h3.congr (Eventually.of_forall fun t => ?_)
    simp only [Function.comp_apply, hf]
    rw [← h.expG_add_smul, add_sub_cancel]

  have hder : ∀ k, iteratedDeriv k f 0 = 0 := by
    intro k
    rw [hf, h.iteratedDeriv_coeff_line π (hS v hv) ℓ Y k]
    simp only [zero_smul, h.expG_zero, BanachRep.map_one, one_apply_eq_self]
    rw [hℓ]
    refine hw _ ?_
    clear hf han
    induction k with
    | zero => exact hv
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact hSd Y _ ih
  have := eq_zero_of_iteratedDeriv_eq_zero han hder 1
  simp only [hf, one_smul] at this
  rw [hℓ] at this
  exact this

end IsExpLieAlgebra

end GroundTheory.Automorphic
