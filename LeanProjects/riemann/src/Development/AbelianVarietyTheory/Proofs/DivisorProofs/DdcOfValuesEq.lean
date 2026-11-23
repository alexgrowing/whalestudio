import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPosFrameQuotIn
open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecForm.DdcValues

variable {n : ℕ}

theorem coefwise_del_sum {ι : Type} [Fintype ι] {g : ι → V n → ℂ} (w : ι → Alt n) {β : V n → Alt n} {v : V n}
    (hg : ∀ i, DifferentiableAt ℝ (g i) v) (hβ : ∀ᶠ x in 𝓝 v, β x = ∑ i, g i x • w i) (ξ : V n) :
    coefwise (fun f => del f v ξ) β = ∑ i, del (g i) v ξ • w i := by
  have h (S) : del (fun x => (bas n).repr (β x) S) v ξ = ∑ i, del (g i) v ξ * (bas n).repr (w i) S := by
    have e : (fun x => (bas n).repr (β x) S) =ᶠ[𝓝 v] fun x => ∑ i, (bas n).repr (w i) S • g i x :=
      hβ.mono fun x hx => by simp [hx, Finsupp.finsetSum_apply, mul_comm]
    rw [del_congr e, del_sum (A := fun i x => (bas n).repr (w i) S • g i x) (fun i _ => (hg i).const_smul ((bas n).repr (w i) S)), ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [del_const_smul _ (hg i)]
    simp [mul_comm]
  simp only [coefwise, h, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_smul, ← Finset.smul_sum, Module.Basis.sum_repr]

theorem coefwise_dbar_sum {ι : Type} [Fintype ι] {g : ι → V n → ℂ} (w : ι → Alt n) {v : V n}
    (hg : ∀ i, DifferentiableAt ℝ (g i) v) (ξ : V n) :
    coefwise (fun f => dbar f v ξ) (fun x => ∑ i, g i x • w i) = ∑ i, dbar (g i) v ξ • w i := by
  have h (S) : dbar (fun x => (bas n).repr (∑ i, g i x • w i) S) v ξ =
      ∑ i, dbar (g i) v ξ * (bas n).repr (w i) S := by
    have e : (fun x => (bas n).repr (∑ i, g i x • w i) S) = fun x => ∑ i, (bas n).repr (w i) S • g i x :=
      funext fun x => by simp [Finsupp.finsetSum_apply, mul_comm]
    rw [e, dbar_sum (A := fun i x => (bas n).repr (w i) S • g i x) (fun i _ => (hg i).const_smul ((bas n).repr (w i) S)), ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dbar_const_smul _ (hg i)]
    simp [mul_comm]
  simp only [coefwise, h, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_smul, ← Finset.smul_sum, Module.Basis.sum_repr]

theorem sym_mul_sym_swap (a b c d : Fin n) : sym (a, b) * sym (c, d) = -(sym (a, d) * sym (c, b)) := by
  apply Subtype.ext
  change dz a * dzb b * (dz c * dzb d) = -(dz a * dzb d * (dz c * dzb b))
  have h₁ : dzb b * (dz c * dzb d) = dz c * dzb d * dzb b :=
    Subalgebra.mem_center_iff.1 (sym (c, d)).2 _
  have h₂ : dzb d * (dz c * dzb b) = dz c * dzb b * dzb d :=
    Subalgebra.mem_center_iff.1 (sym (c, b)).2 _
  have h₃ : dzb d * dzb b = -(dzb b * dzb d) :=
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
  rw [mul_assoc, mul_assoc, h₁, h₂, mul_assoc, mul_assoc, h₃]
  simp only [mul_neg]

theorem sum_four (D : Fin n → Fin n → Fin n → Fin n → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, (D a b c d + D c d a b - D a d c b - D c b a d) • (sym (a, b) * sym (c, d)) =
      (4 : ℂ) • ∑ a, ∑ b, ∑ c, ∑ d, D a b c d • (sym (a, b) * sym (c, d)) := by
  have P (F : Fin n → Fin n → Fin n → Fin n → Ev n) : ∑ a, ∑ b, ∑ c, ∑ d, F a b c d =
      ∑ p : Fin n × Fin n × Fin n × Fin n, F p.1 p.2.1 p.2.2.1 p.2.2.2 := by
    simp only [Fintype.sum_prod_type]
  rw [P, P]
  simp only [sub_smul, add_smul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  set T := ∑ p : Fin n × Fin n × Fin n × Fin n,
    D p.1 p.2.1 p.2.2.1 p.2.2.2 • (sym (p.1, p.2.1) * sym (p.2.2.1, p.2.2.2)) with hT
  have h₂ : ∑ p : Fin n × Fin n × Fin n × Fin n,
      D p.2.2.1 p.2.2.2 p.1 p.2.1 • (sym (p.1, p.2.1) * sym (p.2.2.1, p.2.2.2)) = T :=
    Fintype.sum_equiv ⟨fun p => (p.2.2.1, p.2.2.2, p.1, p.2.1), fun p => (p.2.2.1, p.2.2.2, p.1, p.2.1),
      fun _ => rfl, fun _ => rfl⟩ _ _ fun p => by simp [mul_comm]
  have h₃ : ∑ p : Fin n × Fin n × Fin n × Fin n,
      D p.1 p.2.2.2 p.2.2.1 p.2.1 • (sym (p.1, p.2.1) * sym (p.2.2.1, p.2.2.2)) = -T := by
    rw [hT, ← Finset.sum_neg_distrib]
    exact Fintype.sum_equiv ⟨fun p => (p.1, p.2.2.2, p.2.2.1, p.2.1), fun p => (p.1, p.2.2.2, p.2.2.1, p.2.1),
      fun _ => rfl, fun _ => rfl⟩ _ _ fun p => by rw [sym_mul_sym_swap, smul_neg]; rfl
  have h₄ : ∑ p : Fin n × Fin n × Fin n × Fin n,
      D p.2.2.1 p.2.1 p.1 p.2.2.2 • (sym (p.1, p.2.1) * sym (p.2.2.1, p.2.2.2)) = -T := by
    rw [hT, ← Finset.sum_neg_distrib]
    exact Fintype.sum_equiv ⟨fun p => (p.2.2.1, p.2.1, p.1, p.2.2.2), fun p => (p.2.2.1, p.2.1, p.1, p.2.2.2),
      fun _ => rfl, fun _ => rfl⟩ _ _ fun p => by rw [sym_mul_sym_swap, smul_neg, mul_comm]; rfl
  rw [h₂, h₃, h₄]
  module

end GlobalTheory.SecForm.DdcValues

namespace GlobalTheory.SecForm

open DdcValues

theorem ddc_ofValues {n : ℕ} (α : V n → V n → V n → ℂ) (v : V n)
    (h : ∀ a b, ContDiffAt ℝ 2 (fun x => α x (coordVec a) (coordVec b)) v) :
    kappa • delAt (dbarAt fun x => (ofValues (α x) : Alt n)) v = (ofValuesTwo (ddcForm α v) : Alt n) := by
  set f : Fin n × Fin n → V n → ℂ := fun p x => α x (coordVec p.1) (coordVec p.2) with hf
  have e₀ : (fun x => (ofValues (α x) : Alt n)) = fun x => ∑ p, f p x • (sym p : Alt n) := by
    funext x
    simp only [ofValues, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul, Fintype.sum_prod_type, hf]
  have hev : ∀ᶠ x in 𝓝 v, ∀ p, DifferentiableAt ℝ (f p) x :=
    eventually_all.2 fun p => ((h p.1 p.2).eventually (by simp)).mono fun x hx => hx.differentiableAt (by simp)
  have e₁ : ∀ᶠ x in 𝓝 v, dbarAt (fun x => (ofValues (α x) : Alt n)) x =
      ∑ q : Fin n × Fin n × Fin n, dbar (f q.2) x (coordVec q.1) • (dzb q.1 * sym q.2) := by
    filter_upwards [hev] with x hx
    rw [e₀, dbarAt, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [coefwise_dbar_sum _ hx, Finset.mul_sum]
    simp only [mul_smul_comm]
  have hd (q : Fin n × Fin n × Fin n) : DifferentiableAt ℝ (fun x => dbar (f q.2) x (coordVec q.1)) v := by
    have h1 := (h q.2.1 q.2.2).fderiv_right (m := 1) (by norm_num)
    simp only [dbar_apply]
    exact (((h1.clm_apply contDiffAt_const).add
      ((h1.clm_apply contDiffAt_const).const_smul Complex.I)).const_smul (1 / 2 : ℂ)).differentiableAt one_ne_zero
  have e₂ : delAt (dbarAt fun x => (ofValues (α x) : Alt n)) v =
      ((∑ a, ∑ b, ∑ c, ∑ d, ddbar (f (c, d)) v (coordVec a) (coordVec b) • (sym (a, b) * sym (c, d)) : Ev n) :
        Alt n) := by
    simp only [delAt, coefwise_del_sum _ hd e₁, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul,
      Subalgebra.coe_mul, Fintype.sum_prod_type, Finset.mul_sum, mul_smul_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    rw [ddbar_eq_del_dbar (h c d), ← mul_assoc]
    rfl
  rw [e₂, ← Subalgebra.coe_smul]
  congr 1
  have := sum_four fun a b c d => ddbar (f (c, d)) v (coordVec a) (coordVec b)
  simp only [ofValuesTwo, ddcForm, mul_smul, ← Finset.smul_sum]
  erw [this]
  module

end GlobalTheory.SecForm
