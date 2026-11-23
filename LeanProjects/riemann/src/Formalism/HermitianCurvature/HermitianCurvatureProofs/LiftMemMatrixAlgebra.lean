import Formalism.HermitianCurvature.CompositeFormulaLevelZero

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T

section MatSub

variable {A : Type} [Ring A] [Algebra ℂ A]

def matSub (C : Subalgebra ℂ A) (n : Type) [Fintype n] [DecidableEq n] : Subalgebra ℂ (Matrix n n A) where
  carrier := {M | ∀ i j, M i j ∈ C}
  mul_mem' := by
    intro M N hM hN i j
    rw [Matrix.mul_apply]
    exact Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ (hM i k) (hN k j)
  add_mem' := by
    intro M N hM hN i j
    exact Subalgebra.add_mem _ (hM i j) (hN i j)
  algebraMap_mem' := by
    intro c i j
    rw [Matrix.algebraMap_matrix_apply]
    split_ifs
    · exact C.algebraMap_mem c
    · exact C.zero_mem

theorem mem_matSub {C : Subalgebra ℂ A} {n : Type} [Fintype n] [DecidableEq n] {M : Matrix n n A} :
    M ∈ matSub C n ↔ ∀ i j, M i j ∈ C := by
  exact Iff.rfl

variable {S : Type} [Fintype S] [DecidableEq S] (C : Subalgebra ℂ A)

theorem eU_mem (a : S) (i j : Fin 2) : (eU a i j : SlopeTestRemainingChoices S A) ∈ matSub C (Ix S) := by
  rw [mem_matSub]
  intro x y
  simp only [eU, Matrix.of_apply]
  split_ifs
  · exact C.one_mem
  · exact C.zero_mem

theorem io_mem {x : A} (hx : x ∈ C) : (io x : SlopeTestRemainingChoices S A) ∈ matSub C (Ix S) := by
  rw [mem_matSub]
  intro i j
  simp only [io, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · exact hx
  · exact C.zero_mem

theorem lift_mem_matrix_algebra {M : M2 A} (hM : ∀ i j, M i j ∈ C) :
    (lift0 M : M2 (SlopeTestRemainingChoices S A)) ∈ matSub (matSub C (Ix S)) (Fin 2) := by
  rw [mem_matSub]
  intro i j
  simp only [lift0, Matrix.map_apply]
  exact io_mem C (hM i j)

theorem ins_mem (a : S) {M : M2 (SlopeTestRemainingChoices S A)} (hM : M ∈ matSub (matSub C (Ix S)) (Fin 2)) :
    ins a M ∈ matSub C (Ix S) := by
  unfold ins
  refine Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (eU_mem C a i j) ?_
  exact mem_matSub.1 hM i j

theorem transpose_mem {n : Type} [Fintype n] [DecidableEq n] {C' : Subalgebra ℂ A} {M : Matrix n n A}
    (hM : M ∈ matSub C' n) : Mᵀ ∈ matSub C' n := by
  exact mem_matSub.2 fun i j => mem_matSub.1 hM j i

theorem Rh0_mem (a : S) (D : ℂ) : (Rh0 a D : M2 (SlopeTestRemainingChoices S A)) ∈ matSub (matSub C (Ix S)) (Fin 2) := by
  have hP : (P0 a : M2 (SlopeTestRemainingChoices S A)) ∈ matSub (matSub C (Ix S)) (Fin 2) :=
    mem_matSub.2 fun i j => eU_mem C a j i
  unfold Rh0
  exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (Subalgebra.smul_mem _ (Subalgebra.one_mem _) D) hP) _

theorem Rht0_mem (a : S) (D : ℂ) : (Rht0 a D : M2 (SlopeTestRemainingChoices S A)) ∈ matSub (matSub C (Ix S)) (Fin 2) := by
  have hQ : (Q0 a : M2 (SlopeTestRemainingChoices S A)) ∈ matSub (matSub C (Ix S)) (Fin 2) :=
    mem_matSub.2 fun i j => eU_mem C a i j
  unfold Rht0
  exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (Subalgebra.smul_mem _ (Subalgebra.one_mem _) D) hQ) _

theorem TTw_mem {QQ : ℂ → M2 A} (hQ : ∀ Y i j, QQ Y i j ∈ C) (w : List (Letter ℂ S)) (Y : ℂ) :
    TTw QQ w Y ∈ matSub (matSub C (Ix S)) (Fin 2) := by
  induction w generalizing Y with
  | nil =>
    simp only [TTw]
    exact lift_mem_matrix_algebra C (hQ Y)
  | cons l w ih =>
    simp only [TTw]
    split_ifs
    · exact Subalgebra.mul_mem _ (ih Y) (Rh0_mem C _ _)
    · exact Subalgebra.mul_mem _ (Rht0_mem C _ _) (ih Y)

theorem RRw_mem {QQ : ℂ → M2 A} (hQ : ∀ Y i j, QQ Y i j ∈ C) (w : List (Letter ℂ S)) :
    RRw QQ w ∈ matSub C (Ix S) := by
  induction w with
  | nil =>
    simp only [RRw]
    exact Subalgebra.one_mem _
  | cons l w ih =>
    simp only [RRw]
    refine Subalgebra.mul_mem _ ih (ins_mem C _ ?_)
    split_ifs
    · exact TTw_mem C hQ w _
    · exact transpose_mem (TTw_mem C hQ w _)

theorem commute_io {f : A} {M : SlopeTestRemainingChoices S A} (hM : M ∈ matSub (Subalgebra.centralizer ℂ {f}) (Ix S)) :
    Commute (io f : SlopeTestRemainingChoices S A) M := by
  have h : ∀ i j, f * M i j = M i j * f := by
    intro i j
    have hm := mem_matSub.1 hM i j
    rw [Subalgebra.mem_centralizer_iff] at hm
    exact hm f (Set.mem_singleton f)
  show (io f : SlopeTestRemainingChoices S A) * M = M * io f
  ext i j
  simp only [io, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact h i j

end MatSub

section Act

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem pr_fst_sum {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} (s : Finset ι) (g : ι → Pr V) :
    (∑ i ∈ s, g i).1 = ∑ i ∈ s, (g i).1 := by
  first
    | exact Prod.fst_sum (s := s) (f := g)
    | (classical
       induction s using Finset.induction_on with
       | empty => simp only [Finset.sum_empty]; rfl
       | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl)

theorem pr_fst_mul {V : Type} [AddCommGroup V] [Module ℂ V] (m n : Pr V) : (m * n).1 = m.1 * n.1 := rfl

theorem pr_fst_zero {V : Type} [AddCommGroup V] [Module ℂ V] : (0 : Pr V).1 = 0 := rfl

theorem act_mul (M N : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (x : Ix S → RadSp k r z z' π π') :
    act (M * N) x = act M (act N x) := by
  funext a
  simp only [act, Matrix.mul_apply, pr_fst_sum, pr_fst_mul, LinearMap.sum_apply, Module.End.mul_apply,
    map_sum]
  exact Finset.sum_comm

theorem act_io (f : Pr (RadSp k r z z' π π')) (x : Ix S → RadSp k r z z' π π') (a : Ix S) :
    act (io f) x a = f.1 (x a) := by
  simp only [act, io, Matrix.scalar_apply, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    rw [if_neg (Ne.symm hb), pr_fst_zero, LinearMap.zero_apply]
  · intro h
    exact absurd (Finset.mem_univ a) h

end Act

section Wave

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem hsInner_smul_left (a : ℂ) (U V : Wq →L[ℂ] Wp) : B.hsInner (a • U) V = a * B.hsInner U V := by
  have e : Formalism.FourierDecayAlt.B.hsVec (a • U) = a • Formalism.FourierDecayAlt.B.hsVec U := by
    unfold Formalism.FourierDecayAlt.B.hsVec
    rw [← WithLp.toLp_smul]
    first
      | rfl
      | (congr 1; funext i; simp)
  unfold Formalism.FourierDecayAlt.B.hsInner
  rw [e, inner_smul_right]

theorem pairAt_mulOp (μ : Measure (Mt k r)) (l : Fin r) (s : ℂ) (Wv : Module.End ℂ (RadSp k r z z' π π'))
    (hW : multiplicationOperator Wv (fun c _ => fsv s (c l))) (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    pairAt μ (Wv Φ) Ψ c = fsv s (c l) * pairAt μ Φ Ψ c := by
  unfold pairAt
  simp_rw [hW Φ c, hsInner_smul_left]
  exact MeasureTheory.integral_const_mul _ _

theorem glue_succ_update (l : Fin r) (c : Fin r → ℂ) (t : ℂ) (c' : Cf r l.succ) :
    glue l.succ (Function.update c l t) c' l = t := by
  simp only [glue]
  rw [dif_neg (by rw [Fin.val_succ]; omega)]
  simp

theorem form_mulOp (μ : Measure (Mt k r)) (l : Fin r) (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp k r z z' π π'))
    (hW : multiplicationOperator Wv (fun c _ => fsv s (c l))) (u y : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ) (t : ℂ) :
    form μ l.succ (act (io (mkP Wv Wv')) u) y (Function.update c l t) =
      fsv s t * form μ l.succ u y (Function.update c l t) := by
  unfold form
  have h : ∀ (c' : Cf r l.succ) (a : Ix S), pairAt μ (act (io (mkP Wv Wv')) u a) (y a) (glue l.succ (Function.update c l t) c') =
      fsv s t * pairAt μ (u a) (y a) (glue l.succ (Function.update c l t) c') := by
    intro c' a
    rw [act_io]
    have e : (mkP Wv Wv' : Pr (RadSp k r z z' π π')).1 = Wv := rfl
    rw [e, pairAt_mulOp μ l s Wv hW, glue_succ_update]
  simp_rw [h, ← Finset.mul_sum, mul_left_comm _ (fsv s t)]
  exact MeasureTheory.integral_const_mul _ _

end Wave

section StepParts

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
variable (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
  (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
  (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
  (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)

theorem stepTwistFromParts : StepTwistFromParts (S := S) P z z' π π' X μ L st K l0 := by
  intro hD hPW hWS hWC hWK w hw l s Wv Wv' hW hW' x y hx hy c _
  refine ⟨hWK w hw l s Wv Wv' hW hW' x hx, fun t _ => ?_⟩
  obtain ⟨hwave, hc1, hc2, hp⟩ := hWS hD.2.2.1 l s Wv Wv' hW hW'
  have hbT : bTl L l w * Vw (mkP Wv Wv') s w = io (mkP Wv Wv') * bTl L l w :=
    hPW ℂ _ S (site L l) (mkP Wv Wv') (mkP Wv' Wv) s w hwave hc1 hc2 hp hw.1.1
  have hQ : ∀ Y i j, QQi L st l.succ Y i j ∈ Subalgebra.centralizer ℂ {mkP Wv Wv'} := by
    intro Y i j
    rw [Subalgebra.mem_centralizer_iff]
    rintro g rfl
    exact (hWC l s Wv Wv' hW hW' Y i j).eq
  have hcomm : io (mkP Wv Wv') * RRi L st l.succ w = RRi L st l.succ w * io (mkP Wv Wv') :=
    (commute_io (RRw_mem _ hQ w)).eq
  simp only [P5.ph, RRform]
  rw [← act_mul (bTl L l w) (Vw (mkP Wv Wv') s w) x, hbT, act_mul (io (mkP Wv Wv')) (bTl L l w) x,
    ← act_mul (RRi L st l.succ w) (io (mkP Wv Wv')), ← hcomm, act_mul (io (mkP Wv Wv')), form_mulOp μ l s Wv Wv' hW]
  ring

end StepParts

end Formalism.FourierDecayAlt.P5
