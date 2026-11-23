import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodLiftOnto
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicScalarBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurComponentsSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulNormSqLeNormProjApplySqOfSpanningParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsMultIPOfModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodScalarOfIsAdelicScalar

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowTopBound

theorem idem_apply {G H : Type} [Group G] [Fintype G] [AddCommGroup H] [Module ℂ H] (ρ : Representation ℂ G H) {a : G → ℂ}
    (ha : GlobalTheory.IndefiniteRowSideFullHecke.GoodBasisCentralIdempotents.IsCentralIdem a) (u : H) :
    (∑ g, a g • ρ g : H →ₗ[ℂ] H) ((∑ g, a g • ρ g : H →ₗ[ℂ] H) u) = (∑ g, a g • ρ g : H →ₗ[ℂ] H) u := by
  have h1 : (∑ g, a g • ρ g : H →ₗ[ℂ] H) u = ∑ g, ∑ h, (a h * a (h⁻¹ * g)) • ρ g u := by
    simp only [← Finset.sum_smul, ha.2, LinearMap.sum_apply, LinearMap.smul_apply]
  have h2 : (∑ g, a g • ρ g : H →ₗ[ℂ] H) ((∑ g, a g • ρ g : H →ₗ[ℂ] H) u) = ∑ h, ∑ g, (a h * a g) • ρ h (ρ g u) := by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [h2, h1, Finset.sum_comm (f := fun g h => (a h * a (h⁻¹ * g)) • ρ g u)]
  refine Finset.sum_congr rfl fun h _ => Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
  simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, map_mul, Module.End.mul_apply]

theorem le_eigenvalue {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (T S : X →ₗ[ℂ] Y) (e : Y →ₗ[ℂ] Y) (m l : ℝ)
    (hS : ∀ y, S y = e (T y)) (hee : ∀ y, e (e y) = e y) (hadj : ∀ x, e x = x → ∀ y, ⟪x, e y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hm : ∀ u, m * ‖u‖ ^ 2 ≤ ‖LinearMap.adjoint T u‖ ^ 2) (x : Y) (hx : x ≠ 0) (hl : 0 < l)
    (h : S (LinearMap.adjoint S x) = (l : ℂ) • x) : m ≤ l := by
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have hex : e x = x := by
    refine smul_right_injective Y hl' ?_
    show (l : ℂ) • e x = (l : ℂ) • x
    rw [← map_smul, ← h, hS, hee]
  have h1 : LinearMap.adjoint S x = LinearMap.adjoint T x := ext_inner_right ℂ fun f => by
    rw [LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left, hS, hadj x hex]
  have h2 : ‖LinearMap.adjoint T x‖ ^ 2 = l * ‖x‖ ^ 2 := by
    have h3 : ⟪LinearMap.adjoint S x, LinearMap.adjoint S x⟫_ℂ = (l : ℂ) * ⟪x, x⟫_ℂ := by
      rw [LinearMap.adjoint_inner_left, h, inner_smul_right]
    rw [h1, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h3
    have h4 : ((‖LinearMap.adjoint T x‖ ^ 2 : ℝ) : ℂ) = ((l * ‖x‖ ^ 2 : ℝ) : ℂ) := by
      push_cast; exact h3
    exact_mod_cast h4
  have h5 := hm x
  rw [h2] at h5
  exact le_of_mul_le_mul_right h5 (by positivity)

theorem scalar_of_ne_bot {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (T : X →ₗ[ℂ] Y) (U U' : Y →ₗ[ℂ] X)
    (hU : U' = U) (P P' : Submodule ℂ Y) (hP : P' = P) (m m' : ℝ) (hm : m ≤ m')
    (h : P' ≠ ⊥ → ∃ l : ℝ, 0 < l ∧ (∀ x ∈ P', T (U' x) = (l : ℂ) • x) ∧ m' ≤ Real.log l) :
    ∃ l : ℝ, Real.exp m ≤ l ∧ ∀ y ∈ P, T (U y) = (l : ℂ) • y := by
  subst hU hP
  by_cases hc : P' = ⊥
  · refine ⟨_, le_rfl, fun y hy => ?_⟩
    have h0 : y = 0 := (Submodule.eq_bot_iff _).1 hc y hy
    rw [h0, map_zero, map_zero, smul_zero]
  · obtain ⟨l, hl, h1, h2⟩ := h hc
    exact ⟨l, (Real.le_log_iff_exp_le hl).1 (hm.trans h2), h1⟩

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

include R in

theorem hookPlus_le_mainTerm (i : Fin D.R.m) : GlobalTheory.LiftLower.hookPlus D i ≤ GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.mainTerm D i (sg0 D A) := by
  have hl : ∀ ρ, lab (sg0 D A) ρ = ρ := fun ρ => by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0]; exact GlobalTheory.IndefiniteRowSideFullHecke.LiftFormsMainTerm.lab_base ρ
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.mainTerm GlobalTheory.LiftLower.hookPlus GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.aPlAt
  simp only [hl]
  have hp : ∀ n a, (1 : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf n a : ℝ) := fun n a => by
    have : 0 < GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf n a := GlobalTheory.Survey.LevelVectorSizeBounds.hookProd_pos _
    exact_mod_cast this
  refine Finset.sum_le_sum fun ρ _ => Real.log_le_log (lt_of_lt_of_le one_pos (hp _ _)) ?_
  exact le_mul_of_one_le_right (zero_le_one.trans (hp _ _)) (hp _ _)

end GlobalTheory.LowTopBound

end
