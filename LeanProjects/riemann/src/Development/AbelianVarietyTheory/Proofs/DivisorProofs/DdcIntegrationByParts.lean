import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDelDbarZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorAtDbarOperatorAtLeibnizOfCommute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorAtDbarOperatorAtLinearLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarSumLeibniz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDelOperatorAtSumSmulLeibniz

set_option autoImplicit false

open MeasureTheory Filter
open GlobalTheory GlobalTheory.CxForm GlobalTheory.LineForm
open GlobalTheory.GoodMetric (coordVec)
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Topology

namespace GlobalTheory.CxForm.ByParts

section Point

variable {n : ℕ}

theorem delAt_fun (u : V n → ℂ) (x : V n) :
    delAt (fun y => algebraMap ℂ (Alt n) (u y)) x = ∑ a, del u x (coordVec a) • dz a := by
  simp only [delAt, Algebra.algebraMap_eq_smul_one, ← bas_empty]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [coefwise_smul (by simp), bas_empty, mul_smul_comm, mul_one]

theorem dbarAt_fun (u : V n → ℂ) (x : V n) :
    dbarAt (fun y => algebraMap ℂ (Alt n) (u y)) x = ∑ a, dbar u x (coordVec a) • dzb a := by
  simp only [dbarAt, Algebra.algebraMap_eq_smul_one, ← bas_empty]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [coefwise_smul (by simp), bas_empty, mul_smul_comm, mul_one]

theorem dzb_mul_dz (a b : Fin n) : dzb b * dz a = -(dz a * dzb b) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)

theorem dbarAt_delAt_fun {u : V n → ℂ} {v : V n} (hu : ContDiffAt ℝ 2 u v) :
    dbarAt (delAt fun y => algebraMap ℂ (Alt n) (u y)) v = -delAt (dbarAt fun y => algebraMap ℂ (Alt n) (u y)) v := by
  have hconst := (delAt_dbarAt_linear_local n v).2.2.2.2
  have e₁ : (delAt fun y => algebraMap ℂ (Alt n) (u y)) = fun x => ∑ a, del u x (coordVec a) • dz a :=
    funext (delAt_fun u)
  have e₂ : (dbarAt fun y => algebraMap ℂ (Alt n) (u y)) = fun x => ∑ a, dbar u x (coordVec a) • dzb a :=
    funext (dbarAt_fun u)
  have hd (a : Fin n) : DifferentiableAt ℝ (fun x => del u x (coordVec a)) v := by
    have h1 : DifferentiableAt ℝ (del u) v :=
      (contDiffAt_del (m := 1) hu (by norm_num)).differentiableAt (by simp)
    exact ((ContinuousLinearMap.apply ℂ ℂ (coordVec a)).restrictScalars ℝ).differentiableAt.comp v h1
  rw [e₁, e₂, dbarAt_sum_smul (c := fun a x => del u x (coordVec a)) (F := fun a _ => dz a) hd
      (fun _ _ => differentiableAt_const _),
    DelForm.delAt_sum_smul (fun a x => dbar u x (coordVec a)) (fun a _ => dzb a)
      (fun a => differentiableAt_dbar_apply hu _) (fun _ _ => differentiableAt_const _)]
  simp only [(hconst _).1, (hconst _).2, smul_zero, add_zero, DelForm.dOne, Finset.sum_mul, smul_mul_assoc,
    ← ddbar_eq_dbar_del hu, ← ddbar_eq_del_dbar hu, dzb_mul_dz, smul_neg, Finset.sum_neg_distrib]
  rw [Finset.sum_comm]

end Point

section Manifold

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem target_mem (x : A.Pt) : (A.e x.1.1).target ∈ 𝓝 x.crd :=
  (A.e x.1.1).open_target.mem_nhds (x.ch.map_source x.2)

theorem diff_coef {α : A.Fld} (h : A.IsForm α) (x : A.Pt) (S : Finset (Fin (n + n))) :
    DifferentiableAt ℝ (fun v => (bas n).repr (A.loc α x.1.1 v) S) x.crd :=
  ((h.smooth x.1.1 S).contDiffAt (target_mem A x)).differentiableAt (by simp)

theorem loc_mul (α β : A.Fld) (i : A.ι) : A.loc (α * β) i = fun v => A.loc α i v * A.loc β i v := by
  funext v
  unfold HolAtlas.loc
  split_ifs
  exacts [rfl, (mul_zero _).symm]

theorem loc_del_dbar (α : A.Fld) (i : A.ι) {v : V n} (hv : v ∈ (A.e i).target) :
    A.loc (A.del α) i v = delAt (A.loc α i) v ∧ A.loc (A.dbar α) i v = dbarAt (A.loc α i) v := by
  constructor <;> rw [HolAtlas.loc, dif_pos hv]
  · exact congrArg (delAt (A.loc α i)) ((A.e i).right_inv hv)
  · exact congrArg (dbarAt (A.loc α i)) ((A.e i).right_inv hv)

theorem loc_fn (g : M → ℝ) (i : A.ι) {v : V n} (hv : v ∈ (A.e i).target) :
    A.loc (A.fn g) i =ᶠ[𝓝 v] fun w => algebraMap ℂ (Alt n) (g ((A.e i).symm w) : ℂ) :=
  eventually_of_mem ((A.e i).open_target.mem_nhds hv) fun w hw => by
    rw [HolAtlas.loc, dif_pos hw]
    rfl

theorem dbar_del_fn {g : M → ℝ} (hg : A.SmoothOn Set.univ fun y => (g y : ℂ)) :
    A.dbar (A.del (A.fn g)) = -A.del (A.dbar (A.fn g)) := by
  funext x
  have hgerm := fun v => (delAt_dbarAt_linear_local n v).2.2.2.1
  have h₁ : A.loc (A.del (A.fn g)) x.1.1 =ᶠ[𝓝 x.crd]
      delAt fun w => algebraMap ℂ (Alt n) (g ((A.e x.1.1).symm w) : ℂ) :=
    eventually_of_mem (target_mem A x) fun v hv =>
      (loc_del_dbar A _ _ hv).1.trans (hgerm v _ _ (loc_fn A g _ hv)).1
  have h₂ : A.loc (A.dbar (A.fn g)) x.1.1 =ᶠ[𝓝 x.crd]
      dbarAt fun w => algebraMap ℂ (Alt n) (g ((A.e x.1.1).symm w) : ℂ) :=
    eventually_of_mem (target_mem A x) fun v hv =>
      (loc_del_dbar A _ _ hv).2.trans (hgerm v _ _ (loc_fn A g _ hv)).2
  have hu : ContDiffAt ℝ 2 (fun w => (g ((A.e x.1.1).symm w) : ℂ)) x.crd :=
    (((hg x.1.1).mono fun v hv => ⟨hv, trivial⟩).contDiffAt (target_mem A x)).of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  rw [Pi.neg_apply, HolAtlas.dbar, HolAtlas.del, (hgerm _ _ _ h₁).2, (hgerm _ _ _ h₂).1]
  exact dbarAt_delAt_fun hu

theorem dbar_del_fn_mul {g : M → ℝ} {ψ : A.Fld} (hd : A.IsForm (A.del (A.fn g))) (hψ : A.IsForm ψ) :
    A.dbar (A.del (A.fn g) * ψ) = A.dbar (A.del (A.fn g)) * ψ - A.del (A.fn g) * A.dbar ψ := by
  funext x
  have key := (FormMul.leibniz_of_comm n (A.loc (A.del (A.fn g)) x.1.1) (A.loc ψ x.1.1) x.crd
    (-A.del (A.fn g) x) (diff_coef A hd x) (diff_coef A hψ x)).2 fun a => by
      rw [A.loc_crd, HolAtlas.del,
        ((delAt_dbarAt_linear_local n _).2.2.2.1 _ _ (loc_fn A g _ (x.ch.map_source x.2))).1, delAt_fun]
      simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, dzb_mul_dz, neg_mul, smul_neg,
        Finset.sum_neg_distrib]
  rw [A.loc_crd ψ x, neg_mul, ← sub_eq_add_neg] at key
  rw [HolAtlas.dbar, loc_mul]
  exact key

end Manifold

theorem integral_fn_mul_ddc : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n) (g : M → ℝ),
    A.SmoothOn Set.univ (fun y => (g y : ℂ)) → ∀ ψ : A.Fld, A.IsForm ψ →
      A.integral (A.fn g * A.ddc ψ) = A.integral (A.ddc (A.fn g) * ψ) := by
  intro M _ _ _ _ _ _ n A g hg ψ hψ
  obtain ⟨-, C, L, -⟩ := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A
  obtain ⟨hfin, hadd, -⟩ := GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous M n A
  have S := GlobalTheory.T.integral_del_dbar_zero M n A
  have add : ∀ α β : A.Fld, A.IsForm α → A.IsForm β → A.integral (α + β) = A.integral α + A.integral β := by
    intro α β hα hβ
    simp only [← wInt_one]
    exact (hadd _ α β hα hβ (fun ε => have := hfin α hα ε; integrable_const _)
      (fun ε => have := hfin β hβ ε; integrable_const _)).2
  have fmul : ∀ {α β : A.Fld}, A.IsForm α → A.IsForm β → A.IsForm (α * β) := fun h h' => (C 0 _ _ h h').2.1
  have fsm : ∀ (c : ℂ) {α : A.Fld}, A.IsForm α → A.IsForm (c • α) := fun c _ h => (C c _ _ h h).2.2.1
  have fdel : ∀ {α : A.Fld}, A.IsForm α → A.IsForm (A.del α) := fun h => (C 0 _ _ h h).2.2.2.1
  have fdbar : ∀ {α : A.Fld}, A.IsForm α → A.IsForm (A.dbar α) := fun h => (C 0 _ _ h h).2.2.2.2.1
  have ha : A.IsForm (A.fn g) := A.isForm_fn hg
  have h₁ := fmul ha (fdbar hψ)
  have h₂ := fmul (fdel ha) hψ
  have e₁ : A.del (A.fn g * A.dbar ψ) = A.del (A.fn g) * A.dbar ψ + A.fn g * A.del (A.dbar ψ) :=
    (L (fun x => algebraMap ℂ (Ev n) (g x.pt)) (A.dbar ψ) ha (fdbar hψ)).1
  have e₂ := dbar_del_fn_mul A (fdel ha) hψ
  rw [dbar_del_fn A hg] at e₂
  have e : A.fn g * A.ddc ψ = A.ddc (A.fn g) * ψ + (A.del (HermFrame.kappa • (A.fn g * A.dbar ψ)) +
      A.dbar (HermFrame.kappa • (A.del (A.fn g) * ψ))) := by
    rw [(C _ _ _ h₁ h₁).2.2.2.2.2.2.2.1, (C _ _ _ h₂ h₂).2.2.2.2.2.2.2.2, e₁, e₂, HolAtlas.ddc, HolAtlas.ddc,
      mul_smul_comm, smul_mul_assoc, ← smul_add, ← smul_add, neg_mul]
    congr 1
    abel
  have k₁ := fsm HermFrame.kappa h₁
  have k₂ := fsm HermFrame.kappa h₂
  have k₀ : A.IsForm (A.ddc (A.fn g) * ψ) := fmul (fsm HermFrame.kappa (fdel (fdbar ha))) hψ
  rw [e, add _ _ k₀ (C 0 _ _ (fdel k₁) (fdbar k₂)).1, add _ _ (fdel k₁) (fdbar k₂),
    (S _ k₁).1, (S _ k₂).2, add_zero, add_zero]

end GlobalTheory.CxForm.ByParts
