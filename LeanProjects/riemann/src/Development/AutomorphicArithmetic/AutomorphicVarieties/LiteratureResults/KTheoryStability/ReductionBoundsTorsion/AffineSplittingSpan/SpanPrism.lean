import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.Transfer
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DcCons

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.PrismSpan

open PositivityTheory.KB.SplitAffineSpectral

variable {Y : Type}

def prism (φ : Y → Y) : {n : ℕ} → ((Fin (n + 1) → Y) → ℝ) → (Fin n → Y) → ℝ
  | 0, _ => fun _ => 0
  | n + 1, F => fun y => F (Fin.cons (y 0) (fun i => φ (y i))) -
      prism φ (n := n) (fun w => F (Fin.cons (y 0) w)) (Fin.tail y)

theorem prism_succ (φ : Y → Y) {n : ℕ} (F : (Fin (n + 2) → Y) → ℝ) (y : Fin (n + 1) → Y) :
    prism φ F y = F (Fin.cons (y 0) (fun i => φ (y i))) -
      prism φ (fun w => F (Fin.cons (y 0) w)) (Fin.tail y) := rfl

theorem comp_cons' {Z : Type} (φ : Y → Z) {n : ℕ} (a : Y) (w : Fin n → Y) :
    (fun i => φ ((Fin.cons a w : Fin (n + 1) → Y) i)) = Fin.cons (φ a) (fun i => φ (w i)) := by
  funext j; refine Fin.cases ?_ (fun k => ?_) j <;> simp

theorem prism_cons (φ : Y → Y) {n : ℕ} (F : (Fin (n + 2) → Y) → ℝ) (a : Y) (w : Fin n → Y) :
    prism φ F (Fin.cons a w) = F (Fin.cons a (Fin.cons (φ a) (fun i => φ (w i)))) -
      prism φ (fun w' => F (Fin.cons a w')) w := by
  rw [prism_succ]
  simp only [Fin.cons_zero, Fin.tail_cons, comp_cons']

theorem dc_cons {m : ℕ} (F : (Fin (m + 2) → Y) → ℝ) (a : Y) (w : Fin (m + 2) → Y) :
    dc F (Fin.cons a w) = F w - dc (fun w' => F (Fin.cons a w')) w :=
  _root_.UpperTheory.Reformulated.B.Qj27.dc_cons F a w

theorem dc_sub {m : ℕ} (F G : (Fin (m + 1) → Y) → ℝ) : dc (F - G) = dc F - dc G := by
  funext y; simp only [dc, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem dc_add {m : ℕ} (F G : (Fin (m + 1) → Y) → ℝ) : dc (F + G) = dc F + dc G := by
  funext y; simp only [dc, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem dc_smul {m : ℕ} (r : ℝ) (F : (Fin (m + 1) → Y) → ℝ) : dc (r • F) = r • dc F := by
  funext y; simp only [dc, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem dc_zero {m : ℕ} : dc (0 : (Fin (m + 1) → Y) → ℝ) = 0 := by
  funext y; simp [dc]

theorem dc_comp {Z : Type} {m : ℕ} (F : (Fin (m + 1) → Z) → ℝ) (ψ : Y → Z) (y : Fin (m + 2) → Y) :
    dc (fun w => F (fun i => ψ (w i))) y = dc F (fun i => ψ (y i)) := rfl

theorem prism_sub (φ : Y → Y) : ∀ {n : ℕ} (F G : (Fin (n + 1) → Y) → ℝ),
    prism φ (F - G) = prism φ F - prism φ G
  | 0, _, _ => by funext y; simp [prism]
  | n + 1, F, G => by
    funext y
    simp only [prism_succ, Pi.sub_apply]
    have := prism_sub φ (n := n) (fun w => F (Fin.cons (y 0) w)) (fun w => G (Fin.cons (y 0) w))
    have h2 : (fun w => F (Fin.cons (y 0) w) - G (Fin.cons (y 0) w)) =
        (fun w => F (Fin.cons (y 0) w)) - (fun w => G (Fin.cons (y 0) w)) := rfl
    rw [h2, this, Pi.sub_apply]
    ring

theorem prism_dc (φ : Y → Y) : ∀ (m : ℕ) (F : (Fin (m + 2) → Y) → ℝ) (y : Fin (m + 2) → Y),
    dc (prism φ F) y + prism φ (dc F) y = F (fun i => φ (y i)) - F y
  | 0, F, y => by
    simp [dc, prism, Fin.sum_univ_succ, Fin.tail]
    have h1 : (Fin.cons (y 0) (fun i : Fin 1 => φ (y (Fin.succAbove 1 i))) : Fin 2 → Y) =
        fun j => (Fin.cons (y 0) (fun i => φ (y i)) : Fin 3 → Y) (Fin.succAbove 2 j) := by
      funext j; fin_cases j <;> rfl
    have h2 : (fun j => (Fin.cons (y 0) (Fin.cons (y 1) (fun i : Fin 1 => φ (y i.succ)) : Fin 2 → Y) :
        Fin 3 → Y) (Fin.succAbove 1 j)) =
        fun j => (Fin.cons (y 0) (fun i => φ (y i)) : Fin 3 → Y) (Fin.succAbove 1 j) := by
      funext j; fin_cases j <;> rfl
    have h3 : (fun j => (Fin.cons (y 0) (Fin.cons (y 1) (fun i : Fin 1 => φ (y i.succ)) : Fin 2 → Y) :
        Fin 3 → Y) (Fin.succAbove 2 j)) = y := by
      funext j; fin_cases j <;> rfl
    rw [h1, h2, h3]
    ring
  | m + 1, F, y => by
    rw [← Fin.cons_self_tail y]
    set a := y 0
    set w := Fin.tail y
    have ih := prism_dc φ m (fun w' => F (Fin.cons a w')) w
    rw [dc_cons, prism_cons]
    have e1 : (fun w' => prism φ F (Fin.cons a w')) =
        (fun w' => F (Fin.cons a (Fin.cons (φ a) (fun i => φ (w' i))))) -
          prism φ (fun w' => F (Fin.cons a w')) := by
      funext w'; rw [prism_cons]; rfl
    have e2 : (fun w' => dc F (Fin.cons a w')) =
        F - dc (fun w' => F (Fin.cons a w')) := by
      funext w'; rw [dc_cons]; rfl
    rw [e1, e2, dc_sub, prism_sub, dc_cons, dc_cons]
    simp only [Pi.sub_apply]
    rw [comp_cons']
    have e4 : dc (fun w' => F (Fin.cons a (Fin.cons (φ a) (fun i => φ (w' i))))) w =
        dc (fun w' => F (Fin.cons a (Fin.cons (φ a) w'))) (fun i => φ (w i)) := rfl
    rw [e4]
    linarith

theorem mul_cons {P : Type} [Group P] (h a : P) {n : ℕ} (w : Fin n → P) :
    (fun i => h * (Fin.cons a w : Fin (n + 1) → P) i) = Fin.cons (h * a) (fun i => h * w i) := by
  funext j; refine Fin.cases ?_ (fun k => ?_) j <;> simp

theorem prism_mul {P : Type} [Group P] (φ : P → P) (h : P) : ∀ {n : ℕ} (F : (Fin (n + 1) → P) → ℝ)
    (y : Fin n → P), prism φ F (fun i => h * y i) =
      prism (fun z => h⁻¹ * φ (h * z)) (fun z => F (fun i => h * z i)) y
  | 0, _, _ => rfl
  | n + 1, F, y => by
    rw [prism_succ, prism_succ]
    have ih := prism_mul φ h (n := n) (fun w => F (Fin.cons (h * y 0) w)) (Fin.tail y)
    have et : Fin.tail (fun i => h * y i) = fun i => h * Fin.tail y i := rfl
    rw [et, ih, mul_cons]
    congr 1
    · congr 1; congr 1; funext i; simp
    · congr 1; funext z; rw [mul_cons]

theorem prism_inv {P : Type} [Group P] (φ : P → P) (S : Set P) (hφ : ∀ g ∈ S, ∀ z, φ (g * z) = g * φ z)
    {n : ℕ} (F : (Fin (n + 1) → P) → ℝ) (hF : InvS S F) : InvS S (prism φ F) := by
  intro g hg y
  rw [prism_mul]
  have e1 : (fun z => g⁻¹ * φ (g * z)) = φ := by funext z; rw [hφ g hg, inv_mul_cancel_left]
  have e2 : (fun z : Fin (n + 1) → P => F (fun i => g * z i)) = F := by funext z; exact hF g hg z
  rw [e1, e2]

theorem prism_eq_zero_of_set (φ : Y → Y) (S : Set Y) (hφ : ∀ z ∈ S, φ z ∈ S) : ∀ {n : ℕ}
    (F : (Fin (n + 1) → Y) → ℝ) (y : Fin n → Y), (∀ z : Fin (n + 1) → Y, (∀ i, z i ∈ S) → F z = 0) →
      (∀ i, y i ∈ S) → prism φ F y = 0
  | 0, _, _, _, _ => rfl
  | n + 1, F, y, hF, hy => by
    rw [prism_succ]
    have h1 : F (Fin.cons (y 0) (fun i => φ (y i))) = 0 := by
      apply hF; intro i; refine Fin.cases ?_ (fun k => ?_) i
      · simpa using hy 0
      · simpa using hφ _ (hy k)
    have h2 := prism_eq_zero_of_set φ S hφ (n := n) (fun w => F (Fin.cons (y 0) w)) (Fin.tail y)
      (fun z hz => hF _ (fun i => Fin.cases (by simpa using hy 0) (fun k => by simpa using hz k) i))
      (fun i => hy _)
    rw [h1, h2, sub_zero]

theorem prism_eq_zero_of_head (φ : Y → Y) : ∀ {n : ℕ} (F : (Fin (n + 2) → Y) → ℝ) (y : Fin (n + 1) → Y),
    (∀ z : Fin (n + 2) → Y, z 0 = y 0 → F z = 0) → prism φ F y = 0
  | 0, F, y, hF => by
    rw [prism_succ, hF _ (by simp)]; simp [prism]
  | n + 1, F, y, hF => by
    rw [prism_succ, hF _ (by simp)]
    rw [prism_eq_zero_of_head φ (n := n) (fun w => F (Fin.cons (y 0) w)) (Fin.tail y)
      (fun z _ => hF _ (by simp)), sub_zero]

end PositivityTheory.KB.SplitAffineSpectral.PrismSpan

end
