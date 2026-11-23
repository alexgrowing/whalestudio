import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVnice
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVstep
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WCellMemOmPlus
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellZetaMinors
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainRecursionFromSingleDescent

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBFV

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

section Lift

variable {A : Type} [Ring A] {n : ℕ}

theorem sum_ix_succ {M : Type*} [AddCommMonoid M] (f : Ix (Fin (n + 1)) → M) :
    ∑ z, f z = ∑ i : Fin 2, ∑ e : Ix (Fin n), f (Fin.cons i e) := by
  rw [← Fintype.sum_prod_type']
  symm
  refine Fintype.sum_bijective (fun p : Fin 2 × Ix (Fin n) => (Fin.cons p.1 p.2 : Ix (Fin (n + 1)))) ⟨?_, ?_⟩ _ _
    (fun p => rfl)
  · rintro ⟨i, e⟩ ⟨i', e'⟩ h
    have h' := Fin.cons_injective2 h
    simp only at h'
    rw [h'.1, h'.2]
  · intro z
    exact ⟨(z 0, Fin.tail z), Fin.cons_self_tail z⟩

theorem ix_ext_iff (z z' : Ix (Fin (n + 1))) : z = z' ↔ z 0 = z' 0 ∧ Fin.tail z = Fin.tail z' := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h0, ht⟩
    rw [← Fin.cons_self_tail z, ← Fin.cons_self_tail z', h0, ht]

def liftM (M : SlopeTestRemainingChoices (Fin n) A) : SlopeTestRemainingChoices (Fin (n + 1)) A :=
  Matrix.of fun z z' => if z 0 = z' 0 then M (Fin.tail z) (Fin.tail z') else 0

theorem liftM_apply (M : SlopeTestRemainingChoices (Fin n) A) (z z' : Ix (Fin (n + 1))) :
    liftM M z z' = if z 0 = z' 0 then M (Fin.tail z) (Fin.tail z') else 0 := rfl

theorem liftM_one : liftM (1 : SlopeTestRemainingChoices (Fin n) A) = 1 := by
  ext z z'
  rw [liftM_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases h0 : z 0 = z' 0
  · by_cases ht : Fin.tail z = Fin.tail z'
    · rw [if_pos h0, if_pos ht, if_pos ((ix_ext_iff z z').2 ⟨h0, ht⟩)]
    · rw [if_pos h0, if_neg ht, if_neg (fun h => ht ((ix_ext_iff z z').1 h).2)]
  · rw [if_neg h0, if_neg (fun h => h0 ((ix_ext_iff z z').1 h).1)]

theorem liftM_zero : liftM (0 : SlopeTestRemainingChoices (Fin n) A) = 0 := by
  ext z z'; simp [liftM_apply]

theorem liftM_add (M N : SlopeTestRemainingChoices (Fin n) A) : liftM (M + N) = liftM M + liftM N := by
  ext z z'; simp only [liftM_apply, Matrix.add_apply]; split_ifs <;> simp

theorem liftM_mul (M N : SlopeTestRemainingChoices (Fin n) A) : liftM (M * N) = liftM M * liftM N := by
  ext z z''
  rw [Matrix.mul_apply, sum_ix_succ]
  simp only [liftM_apply, Fin.cons_zero, Fin.tail_cons, Matrix.mul_apply, ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Fin.sum_univ_two]
  by_cases h0 : z 0 = 0 <;> by_cases h1 : z'' 0 = 0
  · simp [h0, h1]
  · have h1' : z'' 0 = 1 := by omega
    simp [h0, h1']
  · have h0' : z 0 = 1 := by omega
    simp [h0', h1]
  · have h0' : z 0 = 1 := by omega
    have h1' : z'' 0 = 1 := by omega
    simp [h0', h1']

def liftRingHomSucc : SlopeTestRemainingChoices (Fin n) A →+* SlopeTestRemainingChoices (Fin (n + 1)) A where
  toFun := liftM
  map_one' := liftM_one
  map_mul' := liftM_mul
  map_zero' := liftM_zero
  map_add' := liftM_add

theorem liftRingHom_apply_eq_liftM (M : SlopeTestRemainingChoices (Fin n) A) : (liftRingHomSucc M : SlopeTestRemainingChoices (Fin (n + 1)) A) = liftM M := rfl

theorem eU_succ (a : Fin n) (i j : Fin 2) : (eU a.succ i j : SlopeTestRemainingChoices (Fin (n + 1)) A) = liftM (eU a i j) := by
  ext x y
  rw [liftM_apply]
  simp only [eU, Matrix.of_apply]
  have key : (x a.succ = i ∧ y a.succ = j ∧ ∀ b, b ≠ a.succ → x b = y b) ↔
      (x 0 = y 0 ∧ (Fin.tail x a = i ∧ Fin.tail y a = j ∧ ∀ b, b ≠ a → Fin.tail x b = Fin.tail y b)) := by
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h3 0 (Fin.succ_ne_zero a).symm, h1, h2, fun b hb => h3 b.succ (fun h => hb (Fin.succ_injective _ h))⟩
    · rintro ⟨h0, h1, h2, h3⟩
      refine ⟨h1, h2, fun b hb => ?_⟩
      exact Fin.cases (motive := fun b => b ≠ a.succ → x b = y b) (fun _ => h0)
        (fun b' hb' => h3 b' (fun h => hb' (by rw [h]))) b hb
  by_cases h0 : x 0 = y 0
  · rw [if_pos h0]
    by_cases h : Fin.tail x a = i ∧ Fin.tail y a = j ∧ ∀ b, b ≠ a → Fin.tail x b = Fin.tail y b
    · rw [if_pos h, if_pos (key.2 ⟨h0, h⟩)]
    · rw [if_neg h, if_neg (fun h' => h (key.1 h').2)]
  · rw [if_neg h0, if_neg (fun h' => h0 (key.1 h').1)]

theorem io_succ (x : A) : (io x : SlopeTestRemainingChoices (Fin (n + 1)) A) = liftM (io x) := by
  ext z z'
  rw [liftM_apply]
  simp only [io, Matrix.scalar_apply, Matrix.diagonal_apply]
  by_cases h0 : z 0 = z' 0
  · by_cases ht : Fin.tail z = Fin.tail z'
    · rw [if_pos h0, if_pos ht, if_pos ((ix_ext_iff z z').2 ⟨h0, ht⟩)]
    · rw [if_pos h0, if_neg ht, if_neg (fun h => ht ((ix_ext_iff z z').1 h).2)]
  · rw [if_neg h0, if_neg (fun h => h0 ((ix_ext_iff z z').1 h).1)]

theorem liftZero_succ_eq_map (M : M2 A) : (lift0 M : M2 (SlopeTestRemainingChoices (Fin (n + 1)) A)) = (lift0 M).map liftM := by
  ext i j; simp [lift0, io_succ]

theorem ins_succ (a : Fin n) (M : M2 (SlopeTestRemainingChoices (Fin n) A)) : ins a.succ (M.map liftM) = liftM (ins a M) := by
  simp only [ins]
  rw [← liftRingHom_apply_eq_liftM, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, liftRingHom_apply_eq_liftM, liftRingHom_apply_eq_liftM, eU_succ, Matrix.map_apply]

def upL (l : Letter ℂ (Fin n)) : Letter ℂ (Fin (n + 1)) := ⟨l.plus, l.intersection_update_fsHerm_neg_one.succ, l.pt⟩

theorem UUiw_succ [Algebra ℂ A] [StarRing A] (s : ℂ) (u : List (Letter ℂ (Fin n))) :
    (UUiw s (u.map upL) : SlopeTestRemainingChoices (Fin (n + 1)) A) = liftM (UUiw s u) := by
  induction u with
  | nil => exact liftM_one.symm
  | cons l u ih =>
    simp only [List.map_cons, UUiw]
    rw [ih, liftM_mul]
    congr 1
    show ins l.intersection_update_fsHerm_neg_one.succ (lift0 (Uinv (if l.plus then s else star s))) = _
    rw [liftZero_succ_eq_map, ins_succ]

theorem positioned_cons (l : C.Letter) (w : List C.Letter) :
    D.positionted (l :: w) = (⟨l.1, 0, (l.2 : ℂ)⟩ : Letter ℂ (Fin (w.length + 1))) :: (D.positionted w).map upL := by
  simp only [D.positionted, List.ofFn_succ, List.map_ofFn]
  rfl

end Lift

section ActU

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {n : ℕ}

theorem act_liftM (M : SlopeTestRemainingChoices (Fin n) (Pr (RadSp k r z z' π π'))) (X : Ix (Fin (n + 1)) → RadSp k r z z' π π')
    (i : Fin 2) (e : Ix (Fin n)) :
    act (liftM M) X (Fin.cons i e) = act M (fun e' => X (Fin.cons i e')) e := by
  have key : ∀ (i' : Fin 2) (e' : Ix (Fin n)), (liftM M (Fin.cons i e) (Fin.cons i' e')).1 (X (Fin.cons i' e')) =
      if i = i' then (M e e').1 (X (Fin.cons i' e')) else 0 := by
    intro i' e'
    rw [liftM_apply, Fin.cons_zero, Fin.cons_zero, Fin.tail_cons, Fin.tail_cons]
    split_ifs <;> rfl
  simp only [act]
  rw [sum_ix_succ]
  simp only [key]
  rw [Fin.sum_univ_two]
  fin_cases i <;> simp

theorem cons_ne_zero_iff (i0 i' : Fin 2) (e e' : Ix (Fin n)) :
    (∀ b : Fin (n + 1), b ≠ 0 → (Fin.cons i0 e : Ix (Fin (n + 1))) b = (Fin.cons i' e' : Ix (Fin (n + 1))) b) ↔
      e = e' := by
  constructor
  · intro h; funext t; exact h t.succ (Fin.succ_ne_zero t)
  · rintro rfl b hb
    obtain ⟨s, rfl⟩ := Fin.exists_succ_eq.2 hb
    simp only [Fin.cons_succ]

theorem insert_unit_matrix_zero_apply {B : Type} [Ring B] (i j i0 : Fin 2) (e : Ix (Fin n)) (z' : Ix (Fin (n + 1))) :
    (eU (0 : Fin (n + 1)) i j : SlopeTestRemainingChoices (Fin (n + 1)) B) (Fin.cons i0 e) z' =
      if i0 = i ∧ z' = Fin.cons j e then 1 else 0 := by
  simp only [eU, Matrix.of_apply, Fin.cons_zero]
  have : (i0 = i ∧ z' 0 = j ∧ ∀ b, b ≠ 0 → (Fin.cons i0 e : Ix (Fin (n + 1))) b = z' b) ↔
      (i0 = i ∧ z' = Fin.cons j e) := by
    rw [← Fin.cons_self_tail z', cons_ne_zero_iff, Fin.cons_zero]
    constructor
    · rintro ⟨h1, h2, h3⟩; rw [h2, ← h3]; exact ⟨h1, rfl⟩
    · rintro ⟨h1, h2⟩
      have h2' := Fin.cons_injective2 h2
      exact ⟨h1, h2'.1, h2'.2.symm⟩
  simp only [this]

theorem act_addM (M N : SlopeTestRemainingChoices (Fin (n + 1)) (Pr (RadSp k r z z' π π'))) (X : Ix (Fin (n + 1)) → RadSp k r z z' π π') :
    act (M + N) X = act M X + act N X := by
  funext a
  simp only [act, Matrix.add_apply, Pi.add_apply, ← Finset.sum_add_distrib]
  rfl

theorem act_zeroM (X : Ix (Fin (n + 1)) → RadSp k r z z' π π') :
    act (0 : SlopeTestRemainingChoices (Fin (n + 1)) (Pr (RadSp k r z z' π π'))) X = 0 := by
  funext a
  simp only [act, Matrix.zero_apply, Pi.zero_apply]
  exact Finset.sum_eq_zero fun _ _ => rfl

theorem act_sumM {ι : Type} (s : Finset ι) (M : ι → SlopeTestRemainingChoices (Fin (n + 1)) (Pr (RadSp k r z z' π π')))
    (X : Ix (Fin (n + 1)) → RadSp k r z z' π π') : act (∑ i ∈ s, M i) X = ∑ i ∈ s, act (M i) X := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact act_zeroM X
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, act_addM, ih]

theorem act_unit_matrix_zero_radial (i j i0 : Fin 2) (W : Ix (Fin (n + 1)) → RadSp k r z z' π π') (e : Ix (Fin n)) :
    act (eU (0 : Fin (n + 1)) i j : SlopeTestRemainingChoices (Fin (n + 1)) (Pr (RadSp k r z z' π π'))) W (Fin.cons i0 e) =
      if i0 = i then W (Fin.cons j e) else 0 := by
  simp only [act, insert_unit_matrix_zero_apply]
  have key : ∀ q : Ix (Fin (n + 1)),
      ((if i0 = i ∧ q = Fin.cons j e then (1 : Pr (RadSp k r z z' π π')) else 0).1) (W q) =
      if q = Fin.cons j e then (if i0 = i then W q else 0) else 0 := by
    intro q
    by_cases h1 : i0 = i <;> by_cases h2 : q = Fin.cons j e <;> simp [h1, h2] <;> rfl
  simp only [key]
  rw [Finset.sum_eq_single (Fin.cons j e) (fun b _ hb => by simp [hb]) (fun h => absurd (Finset.mem_univ _) h)]
  simp

theorem act_insert_numeric_matrix_zero (U : M2 (Pr (RadSp k r z z' π π'))) (W : Ix (Fin (n + 1)) → RadSp k r z z' π π')
    (i0 : Fin 2) (e : Ix (Fin n)) :
    act (ins (0 : Fin (n + 1)) (lift0 U)) W (Fin.cons i0 e) = ∑ j, (U i0 j).1 (W (Fin.cons j e)) := by
  simp only [ins, lift0, Matrix.map_apply]
  rw [act_sumM, Finset.sum_apply]
  simp only [act_sumM, Finset.sum_apply, act_mul, act_unit_matrix_zero_radial, act_io]
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  fin_cases i0 <;> simp

theorem pr_alg_fst_apply (c : ℂ) (Φ : RadSp k r z z' π π') :
    (algebraMap ℂ (Pr (RadSp k r z z' π π')) c).1 Φ = c • Φ := rfl

theorem pr_one_fst_apply (Φ : RadSp k r z z' π π') : (1 : Pr (RadSp k r z z' π π')).1 Φ = Φ := rfl

theorem pr_zero_fst_apply (Φ : RadSp k r z z' π π') : (0 : Pr (RadSp k r z z' π π')).1 Φ = 0 := rfl

theorem uInv_cons {X : Type} [AddCommGroup X] [Module ℂ X] (s : ℂ) (l : C.Letter) (w : List C.Letter)
    (x : Ix (Fin (l :: w).length) → X) (e : Ix (Fin (l :: w).length)) :
    KB.uInv s (l :: w) x e = if e 0 = 0 then KB.uInv s w (fun e' => x (Fin.cons 0 e')) (fun a => e a.succ)
      else KB.uInv s w (fun e' => x (Fin.cons 1 e')) (fun a => e a.succ) +
        (if l.1 then s else conj s) • KB.uInv s w (fun e' => x (Fin.cons 0 e')) (fun a => e a.succ) := rfl

theorem act_UUiw (s : ℂ) : ∀ (w : List C.Letter) (Φ : Ix (Fin w.length) → RadSp k r z z' π π'),
    act (UUiw s (D.positionted w)) Φ = KB.uInv s w Φ
  | [], Φ => by
    funext a
    show act 1 Φ a = Φ a
    simp only [act, Matrix.one_apply]
    rw [Finset.sum_eq_single a (fun b _ hb => by rw [if_neg (Ne.symm hb)]; rfl) (fun h => absurd (Finset.mem_univ a) h)]
    simp
  | l :: w, Φ => by
    funext z0
    obtain ⟨i, e, rfl⟩ : ∃ i e, z0 = (Fin.cons i e : Ix (Fin (w.length + 1))) :=
      ⟨z0 0, Fin.tail z0, (Fin.cons_self_tail z0).symm⟩
    rw [positioned_cons]
    simp only [UUiw]
    rw [UUiw_succ, act_mul, act_insert_numeric_matrix_zero]
    simp only [act_liftM, act_UUiw s w]
    rw [uInv_cons, Fin.sum_univ_two]
    simp only [Fin.cons_zero, Fin.cons_succ]
    fin_cases i
    · simp [Uinv, pr_one_fst_apply, pr_zero_fst_apply]
    · simp [Uinv, pr_one_fst_apply, pr_alg_fst_apply]
      rw [add_comm]

end ActU

theorem uInv_map {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (T : X →ₗ[ℂ] Y) (s : ℂ) :
    ∀ (w : List C.Letter) (x : Ix (Fin w.length) → X) (e : Ix (Fin w.length)),
      T (KB.uInv s w x e) = KB.uInv s w (fun e => T (x e)) e
  | [], x, e => rfl
  | l :: w, x, e => by
    unfold KB.uInv
    split_ifs
    · exact uInv_map T s w _ _
    · rw [map_add, map_smul, uInv_map T s w, uInv_map T s w]
    · rw [map_add, map_smul, uInv_map T s w, uInv_map T s w]

end Formalism.FourierDecayAlt.P.PBFV
