import Formalism.HermitianCurvature.StatementWd
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KroneckerEmbedMulApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QEFirstMulSecondEqSwap

namespace Formalism.FourierDecayAlt.P.Wd5

open Matrix Formalism.FourierDecayAlt.Wd

section Free

variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]

theorem eU_apply (a : S) (i j : Fin 2) (x y : Ix S) :
    (eU a i j : SlopeTestRemainingChoices S A) x y = if x a = i ∧ y = Function.update x a j then 1 else 0 := by
  have key : (x a = i ∧ y a = j ∧ ∀ b, b ≠ a → x b = y b) ↔ (x a = i ∧ y = Function.update x a j) := by
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, funext fun b => ?_⟩
      by_cases hb : b = a
      · subst hb
        simp [h2]
      · simp only [Function.update_apply, if_neg hb]
        exact (h3 b hb).symm
    · rintro ⟨h1, rfl⟩
      exact ⟨h1, by simp, fun b hb => by simp [Function.update_apply, hb]⟩
  simp only [eU, Matrix.of_apply, key]

theorem eU_mul_apply (a : S) (i j : Fin 2) (B : SlopeTestRemainingChoices S A) (x y : Ix S) :
    ((eU a i j : SlopeTestRemainingChoices S A) * B) x y = if x a = i then B (Function.update x a j) y else 0 := by
  rw [Matrix.mul_apply]
  simp only [eU_apply]
  by_cases h : x a = i
  · simp [h, ite_mul, Finset.sum_ite_eq']
  · simp [h]

theorem eU_comm_of_ne {a c : S} (hc : c ≠ a) (i j k l : Fin 2) :
    Commute (eU c i j : SlopeTestRemainingChoices S A) (eU a k l) := by
  show (eU c i j : SlopeTestRemainingChoices S A) * eU a k l = eU a k l * eU c i j
  ext x y
  rw [eU_mul_apply, eU_mul_apply, eU_apply, eU_apply]
  have h1 : Function.update x c j a = x a := by simp [Function.update_apply, Ne.symm hc]
  have h2 : Function.update x a l c = x c := by simp [Function.update_apply, hc]
  have h3 : Function.update (Function.update x c j) a l = Function.update (Function.update x a l) c j :=
    Function.update_comm hc j l x
  rw [h1, h2, h3]
  by_cases hx : x c = i <;> by_cases hy : x a = k <;> simp [hx, hy]

theorem free_io (c : S) (x : A) : FreeOf c (io x : SlopeTestRemainingChoices S A) := by
  intro i j
  show (eU c i j : SlopeTestRemainingChoices S A) * io x = io x * eU c i j
  ext p q
  simp only [io, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, eU, Matrix.of_apply]
  split_ifs <;> simp

theorem free_one (c : S) : FreeOf c (1 : SlopeTestRemainingChoices S A) := fun i j => Commute.one_right _

theorem free_zero (c : S) : FreeOf c (0 : SlopeTestRemainingChoices S A) := fun i j => Commute.zero_right _

theorem free_mul {c : S} {b b' : SlopeTestRemainingChoices S A} (h : FreeOf c b) (h' : FreeOf c b') : FreeOf c (b * b') := fun i j => (h i j).mul_right (h' i j)

theorem free_sub {c : S} {b b' : SlopeTestRemainingChoices S A} (h : FreeOf c b) (h' : FreeOf c b') : FreeOf c (b - b') := fun i j => (h i j).sub_right (h' i j)

theorem free_smul {c : S} {b : SlopeTestRemainingChoices S A} (k : K) (h : FreeOf c b) : FreeOf c (k • b) := by
  intro i j
  show (eU c i j : SlopeTestRemainingChoices S A) * (k • b) = (k • b) * eU c i j
  rw [Matrix.mul_smul, Matrix.smul_mul, (h i j).eq]

theorem free_eU {a c : S} (hc : c ≠ a) (k l : Fin 2) : FreeOf c (eU a k l : SlopeTestRemainingChoices S A) := fun i j => eU_comm_of_ne hc i j k l

theorem freeOf2_mul {c : S} {M N : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 c M) (hN : FreeOf2 c N) :
    FreeOf2 c (M * N) := by
  intro i j p q
  rw [Matrix.mul_apply]
  exact Commute.sum_right _ _ _ fun k _ => (hM i k p q).mul_right (hN k j p q)

theorem freeOf2_transpose {c : S} {M : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 c M) : FreeOf2 c Mᵀ := fun i j => hM j i

theorem freeOf2_one (c : S) : FreeOf2 c (1 : M2 (SlopeTestRemainingChoices S A)) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · exact free_one c
  · exact free_zero c

theorem freeOf2_rmatrix {a c : S} (hc : c ≠ a) (D : K) : FreeOf2 c (Rh0 a D : M2 (SlopeTestRemainingChoices S A)) := by
  intro i j
  simp only [Rh0, Matrix.smul_apply, Matrix.sub_apply]
  exact free_smul _ (free_sub (free_smul _ (freeOf2_one c i j)) (free_eU hc j i))

theorem freeOf2_rmatrix_transpose {a c : S} (hc : c ≠ a) (d : K) : FreeOf2 c (Rht0 a d : M2 (SlopeTestRemainingChoices S A)) := by
  intro i j
  simp only [Rht0, Matrix.smul_apply, Matrix.sub_apply]
  exact free_smul _ (free_sub (free_smul _ (freeOf2_one c i j)) (free_eU hc i j))

theorem free_ins {a c : S} (hc : c ≠ a) {M : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 c M) :
    FreeOf c (ins a M) := by
  intro p q
  unfold ins
  exact Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ =>
    (eU_comm_of_ne hc p q i j).mul_right (hM i j p q)

theorem freeOf2_lift (c : S) (M : M2 A) : FreeOf2 c (lift0 M : M2 (SlopeTestRemainingChoices S A)) := fun i j => free_io c (M i j)

theorem word_free (QQ : K → M2 A) (w : List (Letter K S)) (c : S)
    (hc : c ∉ w.map Letter.intersection_update_fsHerm_neg_one) : FreeOf c (RRw QQ w) ∧ ∀ Y, FreeOf2 c (TTw QQ w Y) := by
  induction w with
  | nil => exact ⟨free_one c, fun Y => freeOf2_lift c (QQ Y)⟩
  | cons l w ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hc
    obtain ⟨hcl, hcw⟩ := hc
    obtain ⟨hR, hT⟩ := ih hcw
    have hT' : ∀ Y, FreeOf2 c (TTw QQ (l :: w) Y) := by
      intro Y
      simp only [TTw]
      split_ifs
      · exact freeOf2_mul (hT Y) (freeOf2_rmatrix hcl _)
      · exact freeOf2_mul (freeOf2_rmatrix_transpose hcl _) (hT Y)
    refine ⟨?_, hT'⟩
    simp only [RRw]
    apply free_mul hR
    apply free_ins hcl
    split_ifs
    · exact hT _
    · exact freeOf2_transpose (hT _)

end Free

theorem wordModule_of (hS : StartModule) (hP : LetterPlus) (hM : LetterMinus) (hF : WordFree) :
    WordModule := by
  intro K A S _ _ _ _ _ _ _ _ QQ q w hQ hw
  induction w with
  | nil =>
    have hset : {Y : K | Reg ([] : List (Letter K S)) Y} = Set.univ := by
      ext Y
      simp [Reg]
    rw [hset]
    exact hS K A S QQ q hQ
  | cons l w ih =>
    obtain ⟨hnd, hreal, hpw⟩ := hw
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.pairwise_cons] at hpw
    have hMod := ih ⟨hnd.2, fun l' hl' => hreal l' (List.mem_cons_of_mem _ hl'), hpw.2⟩
    obtain ⟨hFR, hFT⟩ := hF K A S QQ w l.intersection_update_fsHerm_neg_one hnd.1
    have hmem : l.pt ∈ {Y : K | Reg w Y} := fun l' hl' => hpw.1 l' hl'
    have hstar : star l.pt = l.pt := hreal l (by simp)
    cases hpl : l.plus
    · have key := hM K A S _ _ _ _ l.intersection_update_fsHerm_neg_one l.pt hMod hFR hFT hmem hstar
      convert key using 1
      all_goals first
        | (simp [RRw, hpl]; done)
        | (ext Y; simp [Reg, RegL, TTw, qw, hpl, and_comm]; done)
        | (funext Y; simp [TTw, qw, hpl])
    · have key := hP K A S _ _ _ _ l.intersection_update_fsHerm_neg_one l.pt hMod hFR hFT hmem hstar
      convert key using 1
      all_goals first
        | (simp [RRw, hpl]; done)
        | (ext Y; simp [Reg, RegL, TTw, qw, hpl, and_comm]; done)
        | (funext Y; simp [TTw, qw, hpl])

end Formalism.FourierDecayAlt.P.Wd5

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.Wd

theorem word_free_of_unused_positions : Formalism.FourierDecayAlt.Wd.WordFree := by
  intro K A S _ _ _ _ _ _ _ _ QQ w c hc
  exact Formalism.FourierDecayAlt.P.Wd5.word_free QQ w c hc

theorem word_module_structure : Formalism.FourierDecayAlt.Wd.WordModule := Formalism.FourierDecayAlt.P.Wd5.wordModule_of initial_module_structure letter_module_plus letter_module_minus
  word_free_of_unused_positions

theorem transfer_matrix_factorization : Formalism.FourierDecayAlt.Wd.TTFactor := by
  intro K A S _ _ _ _ _ _ _ _ QQ w Y
  induction w with
  | nil => simp [TTw, Xm, Xp]
  | cons l w ih =>
    simp only [TTw, Xm, Xp]
    split_ifs
    · rw [ih]
      simp only [mul_assoc]
    · rw [ih]
      simp only [mul_assoc]

end Formalism.FourierDecayAlt.P
