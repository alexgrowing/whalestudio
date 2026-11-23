import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.SumFourCommVersion

open Matrix Finset

noncomputable section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem chatAβ {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (w : ℂ) (a : Fin m → ℂ)
    (l : Fin m) : chatA E w a (Pi.single l 1) =
      ∑ j : Fin m, ((-1 : ℂ) ^ ((l : ℕ) + (j : ℕ)) * a j) • qminor E (skip1 l) (skip1 j) w := by
  simp only [chatA]
  rw [Finset.sum_eq_single l (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
  simp

theorem chatAa {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (w : ℂ) (β : Fin m → ℂ)
    (p : Fin m) : chatA E w (Pi.single p 1) β =
      ∑ i : Fin m, ((-1 : ℂ) ^ ((i : ℕ) + (p : ℕ)) * β i) • qminor E (skip1 i) (skip1 p) w := by
  simp only [chatA]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single p (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
  simp

theorem transfer_entry_zero_one {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (Y Yb : Fin m → A)
    (x xb : Fin m → ℂ) (u : ℂ) :
    tA E Y Yb x xb u 0 1 = -∑ l, Yb l * chatA E (u - 1) x (Pi.single l 1) := by
  show -∑ i : Fin m, ∑ j : Fin m,
      ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * x j) • (Yb i * qminor E (skip1 i) (skip1 j) (u - 1)) = _
  simp only [chatAβ, Finset.mul_sum, mul_smul_comm]

theorem transfer_entry_one_zero {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (Y Yb : Fin m → A)
    (x xb : Fin m → ℂ) (u : ℂ) :
    tA E Y Yb x xb u 1 0 = -∑ p, Y p * chatA E u (Pi.single p 1) xb := by
  show -∑ i : Fin m, ∑ j : Fin m,
      ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * xb i) • (Y j * qminor E (skip1 i) (skip1 j) u) = _
  simp only [chatAa, Finset.mul_sum, mul_smul_comm]
  exact congrArg Neg.neg Finset.sum_comm

theorem chatAlinβ {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (w : ℂ)
    (a β : Fin m → ℂ) : chatA E w a β = ∑ l, β l • chatA E w a (Pi.single l 1) := by
  simp only [chatAβ]
  simp only [chatA, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  ring

theorem chatAlina {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (w : ℂ)
    (a β : Fin m → ℂ) : chatA E w a β = ∑ p, a p • chatA E w (Pi.single p 1) β := by
  simp only [chatAa]
  simp only [chatA, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  congr 1
  ring

theorem vecMulSingle {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) (l l' : Fin m) :
    (Pi.single l (1 : ℂ) ᵥ* P) l' = P l l' := by
  first
    | (show ∑ j, (Pi.single l (1 : ℂ) : Fin m → ℂ) j * P j l' = P l l'
       simp [Pi.single_apply])
    | simp [Matrix.vecMul, Pi.single_apply]

theorem mulVecSingle {m : ℕ} (Q : Matrix (Fin m) (Fin m) ℂ) (p p' : Fin m) :
    (Q *ᵥ Pi.single p (1 : ℂ)) p' = Q p' p := by
  first
    | (show ∑ j, Q p' j * (Pi.single p (1 : ℂ) : Fin m → ℂ) j = Q p' p
       simp [Pi.single_apply])
    | simp [Matrix.mulVec, Pi.single_apply]

theorem pull1 {A : Type*} [AddCommMonoid A] {m : ℕ} (g : Fin m → Fin m → Fin m → A) :
    ∑ a, ∑ b, ∑ c, g a b c = ∑ c, ∑ a, ∑ b, g a b c := by
  calc ∑ a, ∑ b, ∑ c, g a b c = ∑ a, ∑ c, ∑ b, g a b c :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, g a b c := Finset.sum_comm

theorem pull6 {A : Type*} [AddCommMonoid A] {m : ℕ} (f : Fin m → Fin m → Fin m → Fin m → Fin m → Fin m → A) :
    ∑ l, ∑ p, ∑ i, ∑ i', ∑ j, ∑ j', f l p i i' j j' = ∑ i, ∑ i', ∑ j, ∑ j', ∑ l, ∑ p, f l p i i' j j' := by
  calc ∑ l, ∑ p, ∑ i, ∑ i', ∑ j, ∑ j', f l p i i' j j'
        = ∑ i, ∑ l, ∑ p, ∑ i', ∑ j, ∑ j', f l p i i' j j' := pull1 _
    _ = ∑ i, ∑ i', ∑ l, ∑ p, ∑ j, ∑ j', f l p i i' j j' :=
        Finset.sum_congr rfl fun i _ => pull1 _
    _ = ∑ i, ∑ i', ∑ j, ∑ l, ∑ p, ∑ j', f l p i i' j j' :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => pull1 _
    _ = ∑ i, ∑ i', ∑ j, ∑ j', ∑ l, ∑ p, f l p i i' j j' :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ =>
          Finset.sum_congr rfl fun j _ => pull1 _

theorem sumSingle {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (W : Fin m → A) (c : Fin m → ℂ) (i i' : Fin m) :
    W i * algebraMap ℂ A (c i') - W i' * algebraMap ℂ A (c i) =
      ∑ l, ((Pi.single l (1 : ℂ) : Fin m → ℂ) i * c i' - (Pi.single l (1 : ℂ) : Fin m → ℂ) i' * c i) • W l := by
  simp [Pi.single_apply, sub_smul, Finset.sum_sub_distrib, ite_smul]
  simp only [Algebra.smul_def, Algebra.commutes]

private theorem sum_mul_sum_mul_eq_sum_sum {A : Type*} [Ring A] {m : ℕ} (f g : Fin m → A) (q : A) :
    (∑ l, f l) * (∑ p, g p) * q = ∑ l, ∑ p, f l * g p * q := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  try (first | rfl | exact Finset.sum_comm)

theorem general_second_minor_expansion {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (W V : Fin m → A) (w : ℂ)
    (a' β' : Fin m → ℂ) :
    ∑ l, ∑ p, W l * V p * chat2A E w (Pi.single p 1) a' (Pi.single l 1) β' =
      ∑ i : Fin m, ∑ i' : Fin m, ∑ j : Fin m, ∑ j' : Fin m,
        if i < i' ∧ j < j' then
          ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ))) •
            ((W i * algebraMap ℂ A (β' i') - W i' * algebraMap ℂ A (β' i)) *
              (V j * algebraMap ℂ A (a' j') - V j' * algebraMap ℂ A (a' j)) *
              qminor E (skip2 i i') (skip2 j j') w)
        else 0 := by
  simp only [chat2A, Finset.mul_sum, mul_ite, mul_zero]
  refine (pull6 _).trans ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ =>
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  by_cases h : i < i' ∧ j < j'
  · simp only [if_pos h]
    rw [sumSingle W β' i i', sumSingle V a' j j', sum_mul_sum_mul_eq_sum_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 1
    ring
  · simp only [if_neg h, Finset.sum_const_zero]

theorem transfer_entry_one_one {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (Y Yb : Fin m → A)
    (x xb : Fin m → ℂ) (u : ℂ) :
    tA E Y Yb x xb u 1 1 = -∑ l, ∑ p, Yb l * Y p * chat2A E (u - 1) (Pi.single p 1) x (Pi.single l 1) xb := by
  rw [general_second_minor_expansion E Yb Y (u - 1) x xb]
  try rfl

private theorem mul_sum_mul_sum_eq_sum_sum {m : ℕ} (a : ℂ) (f g : Fin m → ℂ) :
    a * (∑ l, f l) * (∑ p, g p) = ∑ l, ∑ p, a * f l * g p := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  try (first | rfl | exact Finset.sum_comm)

private theorem sub_mul_eq_sum_single_sub_mul {m : ℕ} (β c : Fin m → ℂ) (i i' : Fin m) :
    β i * c i' - β i' * c i =
      ∑ l, β l * ((Pi.single l (1 : ℂ) : Fin m → ℂ) i * c i' - (Pi.single l (1 : ℂ) : Fin m → ℂ) i' * c i) := by
  simp [Pi.single_apply, mul_sub, Finset.sum_sub_distrib, ite_mul, mul_ite]

theorem chat2Alin {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (w : ℂ)
    (a a' β β' : Fin m → ℂ) :
    chat2A E w a a' β β' = ∑ l, ∑ p, (β l * a p) • chat2A E w (Pi.single p 1) a' (Pi.single l 1) β' := by
  simp only [chat2A, Finset.smul_sum, smul_ite, smul_zero, smul_smul]
  refine Eq.trans ?_ (pull6 _).symm
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ =>
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  by_cases h : i < i' ∧ j < j'
  · simp only [if_pos h]
    simp only [← Finset.sum_smul]
    congr 1
    rw [sub_mul_eq_sum_single_sub_mul β β' i i', sub_mul_eq_sum_single_sub_mul a a' j j', mul_sum_mul_sum_eq_sum_sum]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun p _ => by ring
  · simp only [if_neg h, Finset.sum_const_zero]

private theorem measurePreserving_swap4 {A : Type*} [AddCommMonoid A] {m : ℕ} (g : Fin m → Fin m → Fin m → Fin m → A) :
    ∑ a, ∑ b, ∑ c, ∑ d, g a b c d = ∑ c, ∑ d, ∑ a, ∑ b, g a b c d :=
  (pull1 _).trans (Finset.sum_congr rfl fun _ _ => pull1 _)

theorem tATrans (hCC : ContractionsCovariant) {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ}
    (E : Fin m → Fin m → A) (Y Yb : Fin m → A) (x xb : Fin m → ℂ) (P Q : Matrix (Fin m) (Fin m) ℂ)
    (hGl : GlRel E) (hQP : Q * P = 1) (hPQ : P * Q = 1) (u : ℂ) (p q : Fin 2) :
    tA E Y Yb x xb u p q = tA (Econj E P Q) (vecC Q Y) (covC P Yb) (Q *ᵥ x) (xb ᵥ* P) u p q := by
  have h00 : tA E Y Yb x xb u 0 0 = tA (Econj E P Q) (vecC Q Y) (covC P Yb) (Q *ᵥ x) (xb ᵥ* P) u 0 0 :=
    (hCC A m E P Q hGl hQP hPQ u 0 0 0 0).1.symm
  have h01 : tA E Y Yb x xb u 0 1 = tA (Econj E P Q) (vecC Q Y) (covC P Yb) (Q *ᵥ x) (xb ᵥ* P) u 0 1 := by
    have key : ∀ l', chatA E (u - 1) x (Pi.single l' 1) =
        ∑ l, P l' l • chatA (Econj E P Q) (u - 1) (Q *ᵥ x) (Pi.single l 1) := by
      intro l'
      rw [← (hCC A m E P Q hGl hQP hPQ (u - 1) x x (Pi.single l' 1) (Pi.single l' 1)).2.1, chatAlinβ]
      try simp only [vecMulSingle]
    rw [transfer_entry_zero_one, transfer_entry_zero_one]
    congr 1
    simp only [key, covC, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
    exact Finset.sum_comm
  have h10 : tA E Y Yb x xb u 1 0 = tA (Econj E P Q) (vecC Q Y) (covC P Yb) (Q *ᵥ x) (xb ᵥ* P) u 1 0 := by
    have key : ∀ p', chatA E u (Pi.single p' 1) xb =
        ∑ p, Q p p' • chatA (Econj E P Q) u (Pi.single p 1) (xb ᵥ* P) := by
      intro p'
      rw [← (hCC A m E P Q hGl hQP hPQ u (Pi.single p' 1) (Pi.single p' 1) xb xb).2.1, chatAlina]
      try simp only [mulVecSingle]
    rw [transfer_entry_one_zero, transfer_entry_one_zero]
    congr 1
    simp only [key, vecC, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
    exact Finset.sum_comm
  have h11 : tA E Y Yb x xb u 1 1 = tA (Econj E P Q) (vecC Q Y) (covC P Yb) (Q *ᵥ x) (xb ᵥ* P) u 1 1 := by
    have key : ∀ l' p', chat2A E (u - 1) (Pi.single p' 1) x (Pi.single l' 1) xb =
        ∑ l, ∑ p, (P l' l * Q p p') •
          chat2A (Econj E P Q) (u - 1) (Pi.single p 1) (Q *ᵥ x) (Pi.single l 1) (xb ᵥ* P) := by
      intro l' p'
      rw [← (hCC A m E P Q hGl hQP hPQ (u - 1) (Pi.single p' 1) x (Pi.single l' 1) xb).2.2, chat2Alin]
      try simp only [vecMulSingle, mulVecSingle]
    rw [transfer_entry_one_one, transfer_entry_one_one]
    congr 1
    simp only [key, covC, vecC, Finset.mul_sum, Finset.sum_mul]
    simp only [smul_mul_assoc]
    simp only [mul_smul_comm, smul_mul_assoc, smul_smul]
    refine (measurePreserving_swap4 _).trans ?_
    first
      | rfl
      | exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun p _ => Finset.sum_comm
  fin_cases p <;> fin_cases q
  exacts [h00, h01, h10, h11]

end PI.QnHermHaar
