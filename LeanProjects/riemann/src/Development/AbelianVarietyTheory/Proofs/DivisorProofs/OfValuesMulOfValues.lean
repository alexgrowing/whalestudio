import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPosFrameQuotIn

set_option autoImplicit false

open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.SecForm

private theorem ι_three_swap {W : Type} [AddCommGroup W] [Module ℂ W] (v w x : W) :
    ExteriorAlgebra.ι ℂ v * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ x) =
      -(ExteriorAlgebra.ι ℂ x * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ v)) := by
  have h : ∀ p q : W, ExteriorAlgebra.ι ℂ p * ExteriorAlgebra.ι ℂ q =
      -(ExteriorAlgebra.ι ℂ q * ExteriorAlgebra.ι ℂ p) :=
    fun p q => eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap p q)
  calc ExteriorAlgebra.ι ℂ v * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ x)
      = (ExteriorAlgebra.ι ℂ v * ExteriorAlgebra.ι ℂ w) * ExteriorAlgebra.ι ℂ x := (mul_assoc _ _ _).symm
    _ = -(ExteriorAlgebra.ι ℂ w * (ExteriorAlgebra.ι ℂ v * ExteriorAlgebra.ι ℂ x)) := by
      rw [h v w, neg_mul, mul_assoc]
    _ = (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ x) * ExteriorAlgebra.ι ℂ v := by
      rw [h v x, mul_neg, neg_neg, mul_assoc]
    _ = _ := by rw [h w x, neg_mul, mul_assoc]

theorem sym_mul_sym_swap {n : ℕ} (a b c d : Fin n) :
    (sym (a, b) * sym (c, d) : Ev n) = -(sym (a, d) * sym (c, b)) := by
  apply Subtype.ext
  change dz a * dzb b * (dz c * dzb d) = -(dz a * dzb d * (dz c * dzb b))
  rw [mul_assoc, mul_assoc, ← mul_neg]
  congr 1
  exact ι_three_swap _ _ _

private theorem sum_four {ι R : Type} [Fintype ι] [AddCommMonoid R] (f : ι → ι → ι → ι → R) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ x : ι × ι × ι × ι, f x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  simp only [Fintype.sum_prod_type]

private theorem sum_four_swap_pairs {ι R : Type} [Fintype ι] [AddCommMonoid R] (f : ι → ι → ι → ι → R) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ b, ∑ c, ∑ d, f c d a b := by
  rw [sum_four f, sum_four fun a b c d => f c d a b]
  exact Fintype.sum_equiv ⟨fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1), fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1),
    fun _ => rfl, fun _ => rfl⟩ _ _ fun _ => rfl

private theorem sum_four_swap_second {ι R : Type} [Fintype ι] [AddCommMonoid R] (f : ι → ι → ι → ι → R) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ b, ∑ c, ∑ d, f a d c b := by
  rw [sum_four f, sum_four fun a b c d => f a d c b]
  exact Fintype.sum_equiv ⟨fun x => (x.1, x.2.2.2, x.2.2.1, x.2.1), fun x => (x.1, x.2.2.2, x.2.2.1, x.2.1),
    fun _ => rfl, fun _ => rfl⟩ _ _ fun _ => rfl

private theorem wedge_sum {ι R : Type} [Fintype ι] [CommRing R] [Algebra ℂ R] (s : ι → ι → R)
    (hs : ∀ a b c d, s a b * s c d = -(s a d * s c b)) (α β : ι → ι → ℂ) :
    (∑ a, ∑ b, α a b • s a b) * (∑ a, ∑ b, β a b • s a b) =
      (1 / 4 : ℂ) • ∑ a, ∑ b, ∑ c, ∑ d, wedge α β a b c d • (s a b * s c d) := by
  have h1 : (∑ a, ∑ b, α a b • s a b) * (∑ a, ∑ b, β a b • s a b) =
      ∑ a, ∑ b, ∑ c, ∑ d, (α a b * β c d) • (s a b * s c d) := by
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum, smul_mul_smul_comm]
  have h2 : ∑ a, ∑ b, ∑ c, ∑ d, (α c d * β a b) • (s a b * s c d) =
      ∑ a, ∑ b, ∑ c, ∑ d, (α a b * β c d) • (s a b * s c d) := by
    rw [sum_four_swap_pairs]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => by rw [mul_comm (s c d)]
  have h3 : ∀ γ : ι → ι → ι → ι → ℂ, ∑ a, ∑ b, ∑ c, ∑ d, γ a d c b • (s a b * s c d) =
      -∑ a, ∑ b, ∑ c, ∑ d, γ a b c d • (s a b * s c d) := by
    intro γ
    rw [sum_four_swap_second]
    simp only [← Finset.sum_neg_distrib, ← smul_neg, ← hs]
  have h4 := h3 fun a b c d => α a b * β c d
  have h5 := h3 fun a b c d => α c d * β a b
  rw [h1]
  simp only [wedge, add_smul, sub_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [h4, h5, h2]
  module

theorem ofValues_mul_ofValues {n : ℕ} (α β : V n → V n → ℂ) :
    ofValues α * ofValues β = ofValuesTwo (wedge α β) :=
  wedge_sum (fun a b : Fin n => sym (a, b)) sym_mul_sym_swap
    (fun a b => α (coordVec a) (coordVec b)) (fun a b => β (coordVec a) (coordVec b))

end GlobalTheory.SecForm
