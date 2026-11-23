import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZeroMemSolSet
import Formalism.UnipotentAdelicQuotients.EllRegCheck
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction

noncomputable section

namespace GlobalTheory.VFComp

variable {d : ℕ}

theorem dw_contDiffOn {U : Set (E d)} (hU : IsOpen U) {u : E d → ℂ} (hu : ContDiffOn ℝ ∞ u U) :
    ∀ w : List (Fin d), ContDiffOn ℝ ∞ (dw w u) U
  | [] => hu
  | j :: w => by
    have h := ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 (dw_contDiffOn hU hu w)).2
    exact h.clm_apply contDiffOn_const

theorem diffAt_of {U : Set (E d)} (hU : IsOpen U) {f : E d → ℂ} (hf : ContDiffOn ℝ ∞ f U)
    {x : E d} (hx : x ∈ U) : DifferentiableAt ℝ f x :=
  (((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hf).1).differentiableAt (hU.mem_nhds hx)

def coefB (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (c : Fin d → E d → ℂ)
    (n : ℕ) (w : Fin n → Fin d) (x : E d) : ℂ :=
  if n ≤ m then ∑ j, c j x * fderiv ℝ (a n w) x (ev j) else 0

def coefA (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (c : Fin d → E d → ℂ) :
    (n : ℕ) → (Fin n → Fin d) → E d → ℂ
  | 0, _ => fun _ => 0
  | k + 1, w => fun x => if k ≤ m then c (w 0) x * a k (Fin.tail w) x else 0

def coefVF (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (c : Fin d → E d → ℂ)
    (n : ℕ) (w : Fin n → Fin d) (x : E d) : ℂ :=
  coefA m a c n w x + coefB m a c n w x

theorem sum_cons {M : Type*} [AddCommMonoid M] (k : ℕ) (g : (Fin (k + 1) → Fin d) → M) :
    ∑ w : Fin (k + 1) → Fin d, g w = ∑ j : Fin d, ∑ w : Fin k → Fin d, g (Fin.cons j w) := by
  rw [← (Fin.consEquiv fun _ => Fin d).sum_comp, Fintype.sum_prod_type]
  rfl

end GlobalTheory.VFComp

namespace GlobalTheory.VFComp
variable {d : ℕ}

theorem coefVF_contDiffOn {U : Set (E d)} (hU : IsOpen U) (m : ℕ)
    (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (c : Fin d → E d → ℂ)
    (ha : ∀ n w, ContDiffOn ℝ ∞ (a n w) U) (hc : ∀ j, ContDiffOn ℝ ∞ (c j) U) (n : ℕ) (w : Fin n → Fin d) :
    ContDiffOn ℝ ∞ (coefVF m a c n w) U := by
  have hB : ContDiffOn ℝ ∞ (coefB m a c n w) U := by
    unfold coefB
    split_ifs
    · exact ContDiffOn.sum fun j _ => (hc j).mul (dw_contDiffOn hU (ha n w) [j])
    · exact contDiffOn_const
  have hA : ContDiffOn ℝ ∞ (coefA m a c n w) U := by
    cases n with
    | zero => exact contDiffOn_const
    | succ k =>
      show ContDiffOn ℝ ∞ (fun x => if k ≤ m then c (w 0) x * a k (Fin.tail w) x else 0) U
      split_ifs
      · exact (hc _).mul (ha _ _)
      · exact contDiffOn_const
  exact hA.add hB

theorem symb_coefVF (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (c : Fin d → E d → ℂ)
    (x ξ : E d) : symb (m + 1) (coefVF m a c) x ξ = (∑ j, c j x * ((ξ j : ℝ) : ℂ)) * symb m a x ξ := by
  unfold symb coefVF coefB
  rw [sum_cons, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => ?_
  simp only [coefA, le_refl, if_true, show ¬ (m + 1 ≤ m) by omega, if_false, add_zero, Fin.cons_zero,
    Fin.tail_cons, Fin.prod_univ_succ, Fin.cons_succ]
  ring

end GlobalTheory.VFComp

namespace GlobalTheory.VFComp
variable {d : ℕ}

theorem fderiv_apOp {U : Set (E d)} (hU : IsOpen U) (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ)
    (ha : ∀ n w, ContDiffOn ℝ ∞ (a n w) U) {u : E d → ℂ} (hu : ContDiffOn ℝ ∞ u U) {x : E d} (hx : x ∈ U)
    (j : Fin d) :
    fderiv ℝ (apOp m a u) x (ev j) = ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
      (fderiv ℝ (a n w) x (ev j) * dw (List.ofFn w) u x + a n w x * dw (j :: List.ofFn w) u x) := by
  have hd := HasFDerivAt.sum (u := Finset.range (m + 1)) (x := x)
    (A := fun n => ∑ w : Fin n → Fin d, a n w * dw (List.ofFn w) u) fun n _ =>
      HasFDerivAt.sum (u := Finset.univ) fun w _ =>
        (diffAt_of hU (ha n w) hx).hasFDerivAt.mul
          (diffAt_of hU (dw_contDiffOn hU hu (List.ofFn w)) hx).hasFDerivAt
  have he : apOp m a u = ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d, a n w * dw (List.ofFn w) u := by
    funext y
    simp [apOp, Finset.sum_apply]
  rw [he, hd.fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun w _ => ?_
  simp only [dw]
  ring

end GlobalTheory.VFComp

namespace GlobalTheory.VFComp
variable {d : ℕ}

theorem apOp_coefVF {U : Set (E d)} (hU : IsOpen U) (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ)
    (c : Fin d → E d → ℂ) (ha : ∀ n w, ContDiffOn ℝ ∞ (a n w) U) {u : E d → ℂ} (hu : ContDiffOn ℝ ∞ u U)
    {x : E d} (hx : x ∈ U) :
    ∑ j, c j x * fderiv ℝ (apOp m a u) x (ev j) = apOp (m + 1) (coefVF m a c) u x := by
  have hL : ∑ j, c j x * fderiv ℝ (apOp m a u) x (ev j) =
      (∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
        (∑ j, c j x * fderiv ℝ (a n w) x (ev j)) * dw (List.ofFn w) u x) +
      ∑ n ∈ Finset.range (m + 1), ∑ j : Fin d, ∑ w : Fin n → Fin d,
        c j x * a n w x * dw (j :: List.ofFn w) u x := by
    simp only [fderiv_apOp hU m a ha hu hx, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => ?_
      ring
  have hR : apOp (m + 1) (coefVF m a c) u x =
      (∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
        (∑ j, c j x * fderiv ℝ (a n w) x (ev j)) * dw (List.ofFn w) u x) +
      ∑ n ∈ Finset.range (m + 1), ∑ j : Fin d, ∑ w : Fin n → Fin d,
        c j x * a n w x * dw (j :: List.ofFn w) u x := by
    simp only [apOp, coefVF, add_mul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    · rw [Finset.sum_range_succ]
      have h0 : ∑ w : Fin (m + 1) → Fin d, coefB m a c (m + 1) w x * dw (List.ofFn w) u x = 0 := by
        simp [coefB]
      rw [h0, add_zero]
      refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun w _ => ?_
      have : n ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      simp [coefB, this]
    · rw [Finset.sum_range_succ']
      have h0 : ∑ w : Fin 0 → Fin d, coefA m a c 0 w x * dw (List.ofFn w) u x = 0 := by
        simp [coefA]
      rw [h0, add_zero]
      refine Finset.sum_congr rfl fun n hn => ?_
      have : n ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      rw [sum_cons]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => ?_
      simp [coefA, this, List.ofFn_cons]
  rw [hL, hR]

end GlobalTheory.VFComp

theorem GlobalTheory.VFComp.vectorField_comp : ∀ (d m : ℕ) (U : Set (E d)), IsOpen U → ∀ (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (c : Fin d → E d → ℂ), (∀ n w, ContDiffOn ℝ ∞ (a n w) U) → (∀ j, ContDiffOn ℝ ∞ (c j) U) → ∃ a' : (n : ℕ) → (Fin n → Fin d) → E d → ℂ, (∀ n w, ContDiffOn ℝ ∞ (a' n w) U) ∧ (∀ x ξ : E d, symb (m + 1) a' x ξ = (∑ j, c j x * ((ξ j : ℝ) : ℂ)) * symb m a x ξ) ∧ ∀ u : E d → ℂ, ContDiffOn ℝ ∞ u U → ∀ x ∈ U, ∑ j, c j x * fderiv ℝ (apOp m a u) x (ev j) = apOp (m + 1) a' u x := by
  intro d m U hU a c ha hc
  exact ⟨GlobalTheory.VFComp.coefVF m a c, GlobalTheory.VFComp.coefVF_contDiffOn hU m a c ha hc,
    GlobalTheory.VFComp.symb_coefVF m a c, fun u hu x hx => GlobalTheory.VFComp.apOp_coefVF hU m a c ha hu hx⟩
