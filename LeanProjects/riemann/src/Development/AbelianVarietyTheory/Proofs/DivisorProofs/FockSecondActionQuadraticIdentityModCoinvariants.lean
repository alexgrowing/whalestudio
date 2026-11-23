import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirFockAct1SubCasimirFockAct2
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

noncomputable section

namespace GlobalTheory.HoweR.SecondQuad

section Ring

variable {A : Type} [Ring A] {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  (u l : I × J → A)

theorem left_expand (hlu : ∀ i j, l i * u j = u j * l i + if i = j then 1 else 0) (c e : J) :
    ∑ d, (∑ a, u (a, c) * l (a, d)) * (∑ b, u (b, d) * l (b, e)) =
      ∑ d, ∑ a, ∑ b, u (a, c) * u (b, d) * (l (a, d) * l (b, e)) +
        Fintype.card J • ∑ a, u (a, c) * l (a, e) := by
  have h1 : ∀ d a b, u (a, c) * l (a, d) * (u (b, d) * l (b, e)) =
      u (a, c) * u (b, d) * (l (a, d) * l (b, e)) + if a = b then u (a, c) * l (a, e) else 0 := by
    intro d a b
    have h := hlu (a, d) (b, d)
    simp only [Prod.mk.injEq, and_true] at h
    have : u (a, c) * l (a, d) * (u (b, d) * l (b, e)) = u (a, c) * (l (a, d) * u (b, d)) * l (b, e) := by
      simp only [mul_assoc]
    rw [this, h]
    by_cases hab : a = b
    · subst hab; simp [mul_add, add_mul, mul_assoc]
    · simp [hab, mul_add, add_mul, mul_assoc]
  simp only [Finset.sum_mul_sum, h1, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ]

theorem right_expand (hlu : ∀ i j, l i * u j = u j * l i + if i = j then 1 else 0) (c e : J) :
    ∑ a, ∑ b, (∑ d, u (b, d) * l (a, d)) * (u (a, c) * l (b, e)) =
      ∑ a, ∑ b, ∑ d, u (b, d) * u (a, c) * (l (a, d) * l (b, e)) +
        Fintype.card I • ∑ b, u (b, c) * l (b, e) := by
  have h1 : ∀ a b d, u (b, d) * l (a, d) * (u (a, c) * l (b, e)) =
      u (b, d) * u (a, c) * (l (a, d) * l (b, e)) + if d = c then u (b, c) * l (b, e) else 0 := by
    intro a b d
    have h := hlu (a, d) (a, c)
    simp only [Prod.mk.injEq, true_and] at h
    have : u (b, d) * l (a, d) * (u (a, c) * l (b, e)) = u (b, d) * (l (a, d) * u (a, c)) * l (b, e) := by
      simp only [mul_assoc]
    rw [this, h]
    by_cases hdc : d = c
    · subst hdc; simp [mul_add, add_mul, mul_assoc]
    · simp [hdc, mul_add, add_mul, mul_assoc]
  simp only [Finset.sum_mul, h1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ]

theorem key (hlu : ∀ i j, l i * u j = u j * l i + if i = j then 1 else 0)
    (huu : ∀ i j, u i * u j = u j * u i) (c e : J) :
    ∑ d, (∑ a, u (a, c) * l (a, d)) * (∑ b, u (b, d) * l (b, e)) + Fintype.card I • ∑ a, u (a, c) * l (a, e) =
      ∑ a, ∑ b, (∑ d, u (b, d) * l (a, d)) * (u (a, c) * l (b, e)) +
        Fintype.card J • ∑ a, u (a, c) * l (a, e) := by
  rw [left_expand u l hlu, right_expand u l hlu]
  have hT : ∑ d, ∑ a, ∑ b, u (a, c) * u (b, d) * (l (a, d) * l (b, e)) =
      ∑ a, ∑ b, ∑ d, u (b, d) * u (a, c) * (l (a, d) * l (b, e)) := by
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => by rw [huu]
  rw [hT]
  abel

end Ring

variable {P Q R S : ℕ}

theorem raiB_comm (l m : Ln P Q R S) : raiB l * raiB m = raiB m * raiB l := by
  by_cases hlm : l = m
  · rw [hlm]
  refine LinearMap.ext fun f => ?_
  cases hl : linePos l <;> cases hm : linePos m <;>
    simp [raiB, hl, hm, MvPolynomial.pderiv_X, Pi.single_apply, hlm, Ne.symm hlm,
      GlobalTheory.FockCasimir.pderiv_pderiv_comm l m, mul_left_comm]

theorem fockSecondAction_matrixUnit_eq (c d : Ix R S) :
    fockAct2 P Q R S (Eab c d) = ∑ a, raiB (a, c) * lowB (a, d) +
      if c = d then ((Fintype.card (Ix P Q) : ℂ) / 2) • (1 : Module.End ℂ (Pol P Q R S)) else 0 := by
  rw [fockAct2_Eab]
  simp only [omE, Finset.sum_add_distrib, Prod.mk.injEq, true_and]
  by_cases hcd : c = d
  · simp [hcd, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, div_eq_mul_inv, mul_comm]
  · simp [hcd]

theorem fockFirstAction_matrixUnit_eq (b a : Ix P Q) :
    fockAct1 P Q R S (Eab b a) = ∑ d, raiB (b, d) * lowB (a, d) +
      if b = a then ((Fintype.card (Ix R S) : ℂ) / 2) • (1 : Module.End ℂ (Pol P Q R S)) else 0 := by
  rw [fockAct1_Eab]
  simp only [omE, Finset.sum_add_distrib, Prod.mk.injEq, and_true]
  by_cases hba : b = a
  · simp [hba, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, div_eq_mul_inv, mul_comm]
  · simp [hba]

theorem trace_Eab (b a : Ix P Q) : (Eab b a).trace = if b = a then 1 else 0 := by
  by_cases h : b = a
  · subst h; simp [Eab, Matrix.trace, Matrix.single_apply]
  · simp [Eab, Matrix.trace, Matrix.single_apply, h]

section Alg

variable {A : Type} [Ring A] [Algebra ℂ A] {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem sq_shift (X : J → J → A) (k : ℂ) (c e : J) :
    ∑ d, (X c d + if c = d then k • (1 : A) else 0) * (X d e + if d = e then k • (1 : A) else 0) =
      ∑ d, X c d * X d e + (2 * k) • X c e + if c = e then (k * k) • (1 : A) else 0 := by
  simp only [mul_add, add_mul, Finset.sum_add_distrib, ite_mul, mul_ite, zero_mul, mul_zero,
    smul_mul_assoc, one_mul, mul_smul_comm, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, smul_smul]
  by_cases hce : c = e
  · subst hce; simp only [if_true]; module
  · simp only [hce, if_false]; module

theorem rhs_shift (E : I → I → A) (Y : I → I → A) (m x : ℂ) :
    ∑ a, ∑ b, (E b a + (if b = a then m • (1 : A) else 0) - (x * if b = a then 1 else 0) • (1 : A)) * Y a b =
      ∑ a, ∑ b, E b a * Y a b + (m - x) • ∑ a, Y a a := by
  have : ∀ a b, (E b a + (if b = a then m • (1 : A) else 0) - (x * if b = a then 1 else 0) • (1 : A)) * Y a b =
      E b a * Y a b + if b = a then (m - x) • Y a b else 0 := by
    intro a b
    by_cases h : b = a
    · simp only [h, if_true, mul_one, sub_mul, add_mul, smul_mul_assoc, one_mul, sub_smul]; abel
    · simp [h]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.smul_sum]

end Alg

variable {P Q R S : ℕ}

theorem qop_eq (x : ℂ) (c e : Ix R S) :
    qop (units (fockAct2 P Q R S)) (x + (Fintype.card (Ix R S) : ℂ) / 2)
        ((Fintype.card (Ix P Q) : ℂ) ^ 2 / 4 - (x + (Fintype.card (Ix R S) : ℂ) / 2) * ((Fintype.card (Ix P Q) : ℂ) / 2)) c e =
      ∑ a, ∑ b, (fockAct1 P Q R S (Eab b a) - (x * (Eab b a).trace) • (1 : Module.End ℂ (Pol P Q R S))) *
        (raiB (a, c) * lowB (b, e)) := by
  have hk := key (fun i : Ln P Q R S => raiB i) (fun i => lowB i) GlobalTheory.FockCasimir.lowB_mul_raiB raiB_comm c e
  simp only [← Nat.cast_smul_eq_nsmul ℂ] at hk
  simp only [qop, units, fockSecondAction_matrixUnit_eq, fockFirstAction_matrixUnit_eq, trace_Eab]
  have hs := sq_shift (A := Module.End ℂ (Pol P Q R S)) (fun c d => ∑ a, raiB (a, c) * lowB (a, d))
    ((Fintype.card (Ix P Q) : ℂ) / 2) c e
  have hr := rhs_shift (A := Module.End ℂ (Pol P Q R S)) (fun b a => ∑ d, raiB (b, d) * lowB (a, d))
    (fun a b => raiB (a, c) * lowB (b, e)) ((Fintype.card (Ix R S) : ℂ) / 2) x
  rw [hs, hr]
  by_cases hce : c = e
  · subst hce; simp only [if_true]
    linear_combination (norm := module) hk
  · simp only [hce, if_false]
    linear_combination (norm := module) hk

theorem qop_mem_coinv (P Q R S : ℕ) (x : ℂ) :
    ∃ α β : ℂ, ∀ a b f, qop (units (fockAct2 P Q R S)) α β a b f ∈ coinv P Q R S x := by
  refine ⟨x + (Fintype.card (Ix R S) : ℂ) / 2,
    (Fintype.card (Ix P Q) : ℂ) ^ 2 / 4 - (x + (Fintype.card (Ix R S) : ℂ) / 2) * ((Fintype.card (Ix P Q) : ℂ) / 2),
    fun c e f => ?_⟩
  rw [qop_eq x c e, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun b _ => ?_
  refine Submodule.subset_span ⟨Eab b a, (raiB (a, c) * lowB (b, e)) f, ?_⟩
  simp [Module.End.mul_apply, LinearMap.sub_apply]

end GlobalTheory.HoweR.SecondQuad

end
