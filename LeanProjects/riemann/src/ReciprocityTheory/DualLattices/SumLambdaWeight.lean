import ReciprocityTheory.DualLattices.TensorSpan
import ReciprocityTheory.DualLattices.VIntCastLtOneOfDvd

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.PGsh.Up.U3

open ReciprocityTheory.PGsh.L2

variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]

structure IsTeich (v : Valuation C NNReal) (ω : ZMod p → C) : Prop where
  pow : ∀ a, ω a ^ p = ω a
  cong : ∀ a, v (ω a - (a.val : C)) < 1
  zero : ω 0 = 0
  one : ω 1 = 1
  mul : ∀ a b, ω (a * b) = ω a * ω b
  sep : ∀ a b, a ≠ b → v (ω a - ω b) = 1

namespace IsTeich

variable {ω : ZMod p → C} (hω : IsTeich v ω)
include hω

theorem int (a : ZMod p) : v (ω a) ≤ 1 := by
  by_cases ha : a = 0
  · rw [ha, hω.zero, map_zero]
    exact zero_le
  · have h := hω.sep a 0 ha
    rw [hω.zero, sub_zero] at h
    exact h.le

theorem v_eq_one {a : ZMod p} (ha : a ≠ 0) : v (ω a) = 1 := by
  have h := hω.sep a 0 ha
  rwa [hω.zero, sub_zero] at h

theorem ne_zero {a : ZMod p} (ha : a ≠ 0) : ω a ≠ 0 := by
  intro h
  have h1 := hω.v_eq_one ha
  rw [h, map_zero] at h1
  exact zero_ne_one h1

theorem pow_pred {a : ZMod p} (ha : a ≠ 0) : ω a ^ (p - 1) = 1 := by
  have hne := hω.ne_zero ha
  have h1 : ω a ^ (p - 1) * ω a = 1 * ω a := by
    rw [← pow_succ, Nat.sub_add_cancel hp.out.one_lt.le, one_mul]
    exact hω.pow a
  exact mul_right_cancel₀ hne h1

end IsTeich

def wt (ω : ZMod p → C) (a : ZMod p) : C := ω a ^ (2 * p - 3)

def sS (ω : ZMod p → C) : C := ∑ b, wt ω b

def u0 (ω : ZMod p → C) (a : ZMod p) : C := wt ω a - if a = 0 then sS ω else 0

def lam (ω : ZMod p → C) (f : ZMod p → C) : C := ∑ a, u0 ω a * f a

section wt

namespace IsTeich

variable {ω : ZMod p → C} (hω : IsTeich v ω)
include hω

theorem wt_mul (a b : ZMod p) : wt ω (a * b) = wt ω a * wt ω b := by
  unfold wt
  rw [hω.mul, mul_pow]

theorem wt_zero : wt ω 0 = 0 := by
  unfold wt
  rw [hω.zero]
  exact zero_pow (by have := hp.out.two_le; omega)

theorem wt_mul_self {a : ZMod p} (ha : a ≠ 0) : wt ω a * ω a = 1 := by
  unfold wt
  rw [← pow_succ]
  have e : 2 * p - 3 + 1 = (p - 1) * 2 := by
    have := hp.out.two_le
    omega
  rw [e, pow_mul, hω.pow_pred ha, one_pow]

theorem wt_inv {a : ZMod p} (ha : a ≠ 0) : wt ω a⁻¹ = ω a := by
  have h1 := hω.wt_mul_self (inv_ne_zero ha)
  have h2 : ω a⁻¹ * ω a = 1 := by
    rw [← hω.mul, inv_mul_cancel₀ ha, hω.one]
  calc wt ω a⁻¹ = wt ω a⁻¹ * (ω a⁻¹ * ω a) := by rw [h2, mul_one]
    _ = ω a := by rw [← mul_assoc, h1, one_mul]

theorem wt_int (a : ZMod p) : v (wt ω a) ≤ 1 := by
  unfold wt
  rw [map_pow]
  exact pow_le_one₀ (zero_le) (hω.int a)

private theorem lam_eq_sum_wt_mul_sub (f : ZMod p → C) : lam ω f = ∑ a, wt ω a * (f a - f 0) := by
  simp [lam, u0, sS, sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]

theorem lam_scale (φ : ZMod p → C) (h : ZMod p) :
    ∑ a, u0 ω a * φ (h * a) = ω h * ∑ a, u0 ω a * φ a := by
  have e : ∀ g : ZMod p → C, ∑ a, u0 ω a * g a = ∑ a, wt ω a * (g a - g 0) :=
    fun g => lam_eq_sum_wt_mul_sub hω g
  rw [e (fun a => φ (h * a)), e φ]
  simp only [mul_zero]
  by_cases hh : h = 0
  · subst hh
    simp [hω.zero]
  · rw [Finset.mul_sum]
    calc ∑ a, wt ω a * (φ (h * a) - φ 0)
        = ∑ a, (fun b => wt ω (h⁻¹ * b) * (φ b - φ 0)) (Equiv.mulLeft₀ h hh a) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          simp [inv_mul_cancel_left₀ hh]
      _ = ∑ b, wt ω (h⁻¹ * b) * (φ b - φ 0) := Equiv.sum_comp (Equiv.mulLeft₀ h hh) (fun b => wt ω (h⁻¹ * b) * (φ b - φ 0))
      _ = ∑ b, ω h * (wt ω b * (φ b - φ 0)) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [hω.wt_mul, hω.wt_inv hh]
          ring

theorem lam_eq (f : ZMod p → C) : lam ω f = ∑ a, wt ω a * (f a - f 0) := by
  exact lam_eq_sum_wt_mul_sub hω f

theorem lam_omega : lam ω ω = (p : C) - 1 := by
  rw [lam_eq_sum_wt_mul_sub hω, hω.zero]
  simp only [sub_zero]
  have h1 : ∀ a, wt ω a * ω a = 1 - if a = 0 then 1 else 0 := fun a => by
    split_ifs with ha
    · rw [ha, hω.wt_zero, zero_mul, sub_self]
    · rw [hω.wt_mul_self ha, sub_zero]
  simp only [h1, Finset.sum_sub_distrib]
  simp

end IsTeich

end wt

theorem lam_sum (ω : ZMod p → C) {ι : Type} [Fintype ι] (c : ι → C) (g : ι → ZMod p → C) :
    lam ω (fun a => ∑ j, c j * g j a) = ∑ j, c j * lam ω (g j) := by
  unfold lam
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
  ring

section hopf

variable (hv : v.Integers R)
include hv

theorem cmul_mem {X : Type} (M : Submodule R (X → C)) {c : C} (hc : v c ≤ 1) {f : X → C}
    (hf : f ∈ M) : (fun t => c * f t) ∈ M := by
  obtain ⟨r, hr⟩ := hv.exists_of_le_one hc
  have e : (fun t => c * f t) = r • f := by
    funext t
    simp [Algebra.smul_def, hr]
  rw [e]
  exact M.smul_mem r hf

omit hv in
theorem pow_mem' (AA : HopfOrder (C := C) R (ZMod p)) {f : ZMod p → C} (hf : f ∈ AA.carrier)
    (n : ℕ) : f ^ n ∈ AA.carrier := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact AA.one_mem
  | succ n ih =>
    rw [pow_succ]
    exact AA.mul_mem _ _ ih hf

omit hv in
theorem scale_mem (AA : HopfOrder (C := C) R (ZMod p)) {f : ZMod p → C} (hf : f ∈ AA.carrier)
    (b : ZMod p) : (fun t => f (b * t)) ∈ AA.carrier := by
  have key : ∀ α β : ZMod p → ZMod p,
      (∀ g ∈ AA.carrier, (fun t => g (α t)) ∈ AA.carrier) →
      (∀ g ∈ AA.carrier, (fun t => g (β t)) ∈ AA.carrier) →
      ∀ F ∈ tensorSpan R AA.carrier, (fun t => F (α t, β t)) ∈ AA.carrier := by
    intro α β hα hβ F hF
    induction hF using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, k, hk, rfl⟩ := hx
      exact AA.mul_mem _ _ (hα g hg) (hβ k hk)
    | zero => exact AA.carrier.zero_mem
    | add x y _ _ hx hy => exact AA.carrier.add_mem hx hy
    | smul a x _ hx => exact AA.carrier.smul_mem a hx
  have hn : ∀ n : ℕ, ∀ g ∈ AA.carrier, (fun t => g ((n : ZMod p) * t)) ∈ AA.carrier := by
    intro n
    induction n with
    | zero =>
      intro g hg
      have e : (fun t => g (((0 : ℕ) : ZMod p) * t)) =
          fun t => (addPull R (ZMod p) g) (t, -t) := by
        funext t
        simp [addPull]
      rw [e]
      exact key (fun t => t) (fun t => -t) (fun g hg => hg) (fun g hg => AA.antipode g hg) _
        (AA.comul g hg)
    | succ n ih =>
      intro g hg
      have e : (fun t => g (((n + 1 : ℕ) : ZMod p) * t)) =
          fun t => (addPull R (ZMod p) g) ((n : ZMod p) * t, t) := by
        funext t
        simp [addPull, add_mul]
      rw [e]
      exact key (fun t => (n : ZMod p) * t) (fun t => t) ih (fun g hg => hg) _ (AA.comul g hg)
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have h := hn b.val f hf
  simpa [ZMod.natCast_zmod_val] using h

variable {ω : ZMod p → C} (hω : IsTeich v ω)
include hω

theorem lam_omega_mem (AA : HopfOrder (C := C) R (ZMod p)) {f : ZMod p → C}
    (hf : f ∈ AA.carrier) : (fun t => lam ω f * ω t) ∈ AA.carrier := by
  have hS : v (sS ω) ≤ 1 := by
    unfold sS
    exact v.map_sum_le fun b _ => hω.wt_int b
  have hu : ∀ a, v (u0 ω a) ≤ 1 := fun a => by
    unfold u0
    split_ifs
    · exact (v.map_sub _ _).trans (max_le (hω.wt_int a) hS)
    · rw [sub_zero]
      exact hω.wt_int a
  have key : (fun t => lam ω f * ω t) = ∑ a, (fun t => u0 ω a * f (a * t)) := by
    funext t
    simp only [Finset.sum_apply, lam]
    rw [mul_comm (∑ a, u0 ω a * f a) (ω t), ← hω.lam_scale f t]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_comm t a]
  rw [key]
  exact Submodule.sum_mem _ fun a _ => cmul_mem hv AA.carrier (hu a) (scale_mem AA hf a)

theorem exists_gen (AA : HopfOrder (C := C) R (ZMod p)) [CharZero C] :
    ∃ x1 : C, x1 ≠ 0 ∧ (fun t => x1 * ω t) ∈ AA.carrier ∧
      ∀ f ∈ AA.carrier, ∃ r : R, lam ω f = x1 * algebraMap R C r := by
  obtain ⟨B, hB, hA⟩ := AA.lat
  set b : ZMod p → ZMod p → C := fun j x => B x j with hb
  have hbA : ∀ j, b j ∈ AA.carrier := fun j => by
    rw [hA]
    exact Submodule.subset_span ⟨j, rfl⟩
  obtain ⟨j0, -, hj0⟩ :=
    Finset.exists_max_image Finset.univ (fun j => v (lam ω (b j))) Finset.univ_nonempty
  have hx1 : lam ω (b j0) ≠ 0 := by
    intro h0
    have hall : ∀ j, lam ω (b j) = 0 := fun j => by
      have h := hj0 j (Finset.mem_univ _)
      rw [h0, map_zero] at h
      exact (Valuation.zero_iff v).mp (le_antisymm h (zero_le))
    have hω' : ω = fun a => ∑ j, (B⁻¹ *ᵥ ω) j * b j a := by
      funext a
      have h := congrFun (show B *ᵥ (B⁻¹ *ᵥ ω) = ω by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hB, Matrix.one_mulVec]) a
      rw [← h]
      simp [Matrix.mulVec, dotProduct, hb, mul_comm]
    have hl : lam ω ω = 0 :=
      calc lam ω ω = lam ω (fun a => ∑ j, (B⁻¹ *ᵥ ω) j * b j a) := congrArg (lam ω) hω'
        _ = ∑ j, (B⁻¹ *ᵥ ω) j * lam ω (b j) := lam_sum ω _ b
        _ = 0 := by simp [hall]
    rw [hω.lam_omega] at hl
    exact sub_ne_zero.mpr (Nat.cast_ne_one.mpr hp.out.one_lt.ne') hl
  have hr : ∀ j, ∃ r : R, lam ω (b j) = lam ω (b j0) * algebraMap R C r := fun j => by
    obtain ⟨r, hr⟩ := hv.exists_of_le_one (r := lam ω (b j) / lam ω (b j0)) (by
      rw [map_div₀]
      exact div_le_one_of_le₀ (hj0 j (Finset.mem_univ _)) (zero_le))
    exact ⟨r, by rw [hr]; field_simp⟩
  choose r hr using hr
  refine ⟨lam ω (b j0), hx1, lam_omega_mem hv hω AA (hbA j0), ?_⟩
  intro f hf
  rw [hA] at hf
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hf
  refine ⟨∑ j, c j * r j, ?_⟩
  have e : (∑ i, c i • b i) = fun a => ∑ j, algebraMap R C (c j) * b j a := by
    funext a
    simp [Finset.sum_apply, Algebra.smul_def]
  rw [e, lam_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hr j, map_mul]
  ring

end hopf

end ReciprocityTheory.PGsh.Up.U3
