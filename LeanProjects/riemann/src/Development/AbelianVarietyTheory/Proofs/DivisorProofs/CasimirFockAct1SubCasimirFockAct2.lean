import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.FockCasimir

theorem sum_mul_normal_order {A ι κ : Type} [Ring A] [Algebra ℂ A] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (x d : ι → κ → A)
    (h : ∀ b c e, d b c * x b e = x b e * d b c + if c = e then 1 else 0) :
    ∑ a, ∑ b, (∑ c, (x a c * d b c + if a = b then (1 / 2 : ℂ) • (1 : A) else 0)) *
        (∑ e, (x b e * d a e + if b = a then (1 / 2 : ℂ) • (1 : A) else 0)) =
      (∑ a, ∑ b, ∑ c, ∑ e, x a c * x b e * (d b c * d a e)) +
        ((Fintype.card ι : ℂ) + (Fintype.card κ : ℂ)) • (∑ a, ∑ c, x a c * d a c) +
        ((Fintype.card ι : ℂ) * (Fintype.card κ : ℂ) ^ 2 / 4) • (1 : A) := by
  have h0 : ∀ a b, (∑ c, x a c * d b c) * (∑ e, x b e * d a e) =
      (∑ c, ∑ e, x a c * x b e * (d b c * d a e)) + ∑ c, x a c * d a c := by
    intro a b
    rw [Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    have h1 : ∀ e, x a c * d b c * (x b e * d a e) =
        x a c * x b e * (d b c * d a e) + if c = e then x a c * d a e else 0 := by
      intro e
      have : x a c * d b c * (x b e * d a e) = x a c * (d b c * x b e) * d a e := by
        simp only [mul_assoc]
      rw [this, h, mul_add, add_mul]
      split_ifs <;> simp [mul_assoc]
    simp only [h1, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have h2 : ∀ a b, (∑ c, (x a c * d b c + if a = b then (1 / 2 : ℂ) • (1 : A) else 0)) *
        (∑ e, (x b e * d a e + if b = a then (1 / 2 : ℂ) • (1 : A) else 0)) =
      ((∑ c, ∑ e, x a c * x b e * (d b c * d a e)) + ∑ c, x a c * d a c) +
        if a = b then (Fintype.card κ : ℂ) • (∑ c, x a c * d a c) +
          ((Fintype.card κ : ℂ) ^ 2 / 4) • (1 : A) else 0 := by
    intro a b
    rw [← h0]
    by_cases hab : a = b
    · subst hab
      simp only [if_true, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        ← Nat.cast_smul_eq_nsmul ℂ, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      module
    · simp [hab, Ne.symm hab]
  simp only [h2]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, ← Finset.smul_sum]
  module

variable {p q r s : ℕ}

theorem pderiv_pderiv_comm {σ : Type} (l m : σ) (P : MvPolynomial σ ℂ) :
    pderiv l (pderiv m P) = pderiv m (pderiv l P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P n hP =>
    simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, hP, Pi.single_apply]
    split_ifs <;> simp <;> ring

theorem lowB_comm (l m : Ln p q r s) : lowB l * lowB m = lowB m * lowB l := by
  by_cases hlm : l = m
  · rw [hlm]
  refine LinearMap.ext fun P => ?_
  cases hl : linePos l <;> cases hm : linePos m <;>
    simp [lowB, hl, hm, pderiv_X, Pi.single_apply, hlm, Ne.symm hlm, pderiv_pderiv_comm l m,
      mul_left_comm]

theorem lowB_mul_raiB (l m : Ln p q r s) :
    lowB l * raiB m = raiB m * lowB l + if l = m then 1 else 0 := by
  refine LinearMap.ext fun P => ?_
  by_cases hlm : l = m
  · subst hlm
    cases hl : linePos l <;> simp [lowB, raiB, hl, add_comm]
  · cases hl : linePos l <;> cases hm : linePos m <;>
      simp [lowB, raiB, hl, hm, pderiv_X, Pi.single_apply, hlm, Ne.symm hlm, pderiv_pderiv_comm l m,
        mul_left_comm]

theorem casimir_fockAct1_sub_casimir_fockAct2 : ∀ (p q r s : ℕ),
    casimir (fockAct1 p q r s) - casimir (fockAct2 p q r s) =
      ((((p + q : ℕ) : ℂ) * ((r + s : ℕ) : ℂ) * (((r + s : ℕ) : ℂ) - ((p + q : ℕ) : ℂ))) / 4) •
        (1 : Module.End ℂ (Pol p q r s)) := by
  intro p q r s
  have h1 := sum_mul_normal_order (fun (a : Ix p q) (c : Ix r s) => raiB (a, c))
    (fun (a : Ix p q) (c : Ix r s) => lowB (a, c)) (fun b c e => by simp [lowB_mul_raiB])
  have h2 := sum_mul_normal_order (fun (c : Ix r s) (a : Ix p q) => raiB (a, c))
    (fun (c : Ix r s) (a : Ix p q) => lowB (a, c)) (fun b c e => by simp [lowB_mul_raiB])
  have hQ : (∑ c : Ix r s, ∑ e : Ix r s, ∑ a : Ix p q, ∑ b : Ix p q,
        raiB (a, c) * raiB (b, e) * (lowB (a, e) * lowB (b, c))) =
      ∑ a : Ix p q, ∑ b : Ix p q, ∑ c : Ix r s, ∑ e : Ix r s,
        raiB (a, c) * raiB (b, e) * (lowB (b, c) * lowB (a, e)) := by
    rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type' (α₁ := Ix p q) (α₂ := Ix p q)]
    simp only [← Fintype.sum_prod_type' (α₁ := Ix p q) (α₂ := Ix p q),
      ← Fintype.sum_prod_type' (α₁ := Ix r s) (α₂ := Ix r s)]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [lowB_comm]
  have hE : (∑ c : Ix r s, ∑ a : Ix p q, raiB (a, c) * lowB (a, c)) =
      ∑ a : Ix p q, ∑ c : Ix r s, raiB (a, c) * lowB (a, c) := Finset.sum_comm
  rw [hQ, hE] at h2
  simp only [Formalism.BasicNotions.TH.casimir, fockAct1_Eab, fockAct2_Eab, Formalism.BasicNotions.TH.omE, Prod.mk.injEq, and_true, true_and]
  rw [h1, h2]
  simp only [Fintype.card_sum, Fintype.card_fin]
  module

end GlobalTheory.FockCasimir
