import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff
open GlobalTheory.GoodMetric (coordVec)

namespace GlobalTheory.CxForm.FormMul

variable {n : ℕ}

theorem repr_mul (a b : Alt n) (S : Finset (Fin (n + n))) :
    (bas n).repr (a * b) S = ∑ p : Finset (Fin (n + n)) × Finset (Fin (n + n)),
      (bas n).repr a p.1 * (bas n).repr b p.2 * (bas n).repr (bas n p.1 * bas n p.2) S := by
  conv_lhs => rw [← (bas n).sum_repr a, ← (bas n).sum_repr b]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum, map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [smul_mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem repr_coefwise (T : (V n → ℂ) → ℂ) (H : V n → Alt n) (S : Finset (Fin (n + n))) :
    (bas n).repr (coefwise T H) S = T (fun x => (bas n).repr (H x) S) := by
  simp [coefwise, map_sum, Finsupp.single_apply]

theorem coefwise_mul {v : V n} {T : (V n → ℂ) → ℂ}
    (hsum : ∀ f : Finset (Fin (n + n)) × Finset (Fin (n + n)) → V n → ℂ, (∀ p, DifferentiableAt ℝ (f p) v) →
      T (fun x => ∑ p, f p x) = ∑ p, T (f p))
    (hmul : ∀ f g : V n → ℂ, DifferentiableAt ℝ f v → DifferentiableAt ℝ g v →
      T (fun x => f x * g x) = f v * T g + T f * g v)
    (hconst : ∀ c : ℂ, T (fun _ => c) = 0)
    {F G : V n → Alt n} (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    coefwise T (fun x => F x * G x) = coefwise T F * G v + F v * coefwise T G := by
  refine (bas n).ext_elem fun S => ?_
  have e : (fun x => (bas n).repr (F x * G x) S) = fun x => ∑ p : Finset (Fin (n + n)) × Finset (Fin (n + n)),
      (bas n).repr (F x) p.1 * (bas n).repr (G x) p.2 * (bas n).repr (bas n p.1 * bas n p.2) S :=
    funext fun x => repr_mul _ _ _
  rw [repr_coefwise, e, map_add, Finsupp.add_apply, repr_mul (coefwise T F), repr_mul (F v)]
  simp only [repr_coefwise]
  rw [hsum (fun p x => (bas n).repr (F x) p.1 * (bas n).repr (G x) p.2 * (bas n).repr (bas n p.1 * bas n p.2) S)
    (fun p => ((hF p.1).mul (hG p.2)).mul (differentiableAt_const _)), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hmul (fun x => (bas n).repr (F x) p.1 * (bas n).repr (G x) p.2) (fun _ => (bas n).repr (bas n p.1 * bas n p.2) S)
    ((hF p.1).mul (hG p.2)) (differentiableAt_const _), hconst,
    hmul (fun x => (bas n).repr (F x) p.1) (fun x => (bas n).repr (G x) p.2) (hF p.1) (hG p.2)]
  ring

theorem exists_ι_mul (y : Alt n) : ∃ y' : Alt n, ∀ m, ExteriorAlgebra.ι ℂ m * y = y' * ExteriorAlgebra.ι ℂ m := by
  induction y using ExteriorAlgebra.induction with
  | algebraMap r => exact ⟨algebraMap ℂ _ r, fun m => (Algebra.commutes r _).symm⟩
  | ι x => exact ⟨-ExteriorAlgebra.ι ℂ x, fun m => by
      rw [neg_mul]; exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap m x)⟩
  | mul a b ha hb =>
    obtain ⟨a', ha⟩ := ha
    obtain ⟨b', hb⟩ := hb
    exact ⟨a' * b', fun m => by rw [← mul_assoc, ha, mul_assoc, hb, mul_assoc]⟩
  | add a b ha hb =>
    obtain ⟨a', ha⟩ := ha
    obtain ⟨b', hb⟩ := hb
    exact ⟨a' + b', fun m => by rw [mul_add, ha, hb, add_mul]⟩

theorem sum_mul_leibniz {v : V n} (g : Fin n → (Fin n ⊕ Fin n → ℂ)) (T : Fin n → (V n → ℂ) → ℂ)
    (hsum : ∀ a, ∀ f : Finset (Fin (n + n)) × Finset (Fin (n + n)) → V n → ℂ, (∀ p, DifferentiableAt ℝ (f p) v) →
      T a (fun x => ∑ p, f p x) = ∑ p, T a (f p))
    (hmul : ∀ a, ∀ f g : V n → ℂ, DifferentiableAt ℝ f v → DifferentiableAt ℝ g v →
      T a (fun x => f x * g x) = f v * T a g + T a f * g v)
    (hconst : ∀ a, ∀ c : ℂ, T a (fun _ => c) = 0)
    {F G : V n → Alt n} (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    ∃ y : Alt n, ∑ a, ExteriorAlgebra.ι ℂ (g a) * coefwise (T a) (fun x => F x * G x) =
      (∑ a, ExteriorAlgebra.ι ℂ (g a) * coefwise (T a) F) * G v +
        y * ∑ a, ExteriorAlgebra.ι ℂ (g a) * coefwise (T a) G := by
  obtain ⟨y, hy⟩ := exists_ι_mul (F v)
  refine ⟨y, ?_⟩
  have h (a : Fin n) : ExteriorAlgebra.ι ℂ (g a) * coefwise (T a) (fun x => F x * G x) =
      ExteriorAlgebra.ι ℂ (g a) * coefwise (T a) F * G v + y * (ExteriorAlgebra.ι ℂ (g a) * coefwise (T a) G) := by
    simp only [coefwise_mul (hsum a) (hmul a) (hconst a) hF hG, mul_add, ← mul_assoc, hy]
  rw [Finset.sum_congr rfl fun a _ => h a, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]

theorem delAt_mul {v : V n} {F G : V n → Alt n} (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    ∃ y : Alt n, delAt (fun x => F x * G x) v = delAt F v * G v + y * delAt G v :=
  sum_mul_leibniz (fun a => Pi.single (.inl a) 1) (fun a f => del f v (coordVec a))
    (fun a f hf => by rw [del_sum (fun p _ => hf p), ContinuousLinearMap.sum_apply])
    (fun a f g hf hg => del_mul hf hg _) (fun a c => by rw [del_const]; rfl) hF hG

theorem dbarAt_mul {v : V n} {F G : V n → Alt n} (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    ∃ y : Alt n, dbarAt (fun x => F x * G x) v = dbarAt F v * G v + y * dbarAt G v :=
  sum_mul_leibniz (fun a => Pi.single (.inr a) 1) (fun a f => dbar f v (coordVec a))
    (fun a f hf => by rw [dbar_sum (fun p _ => hf p), ContinuousLinearMap.sum_apply])
    (fun a f g hf hg => dbar_mul hf hg _) (fun a c => by rw [dbar_const]; rfl) hF hG

variable {M : Type} [TopologicalSpace M]

theorem loc_mul (A : HolAtlas M n) (α β : A.Fld) (i : A.ι) (v : V n) :
    A.loc (α * β) i v = A.loc α i v * A.loc β i v := by
  unfold HolAtlas.loc
  split_ifs
  · rfl
  · simp

theorem differentiableAt_coef {A : HolAtlas M n} {α : A.Fld} (h : A.IsForm α) (x : A.Pt) (S : Finset (Fin (n + n))) :
    DifferentiableAt ℝ (fun v => (bas n).repr (A.loc α x.1.1 v) S) x.crd :=
  ((h.smooth x.1.1 S).contDiffAt ((A.e x.1.1).open_target.mem_nhds (x.ch.map_source x.2))).differentiableAt
    (by simp)

end GlobalTheory.CxForm.FormMul
