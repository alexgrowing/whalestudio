import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ConsCompSuccAboveZero
import GroundTheory.ArithmeticGeometry.SchemeCohomology.Cartan
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory Opposite TopologicalSpace

universe u

variable {X : TopCat.{u}} {P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} {R : Type u} [CommRing R]

variable (P) in

structure LocalizingAction (D : R → Opens X) where

  act : R → ∀ W : Opens X, P.obj (op W) →+ P.obj (op W)
  res_act : ∀ (r : R) {V W : Opens X} (h : V ≤ W) (x : P.obj (op W)),
    res P h (act r W x) = act r V (res P h x)
  act_mul : ∀ (a b : R) (W : Opens X) (x : P.obj (op W)), act (a * b) W x = act a W (act b W x)
  act_add : ∀ (a b : R) (W : Opens X) (x : P.obj (op W)), act (a + b) W x = act a W x + act b W x
  act_one : ∀ (W : Opens X) (x : P.obj (op W)), act 1 W x = x
  bijective : ∀ (g : R) (W : Opens X), W ≤ D g → Function.Bijective (act g W)
  kill : ∀ (s t : R) {W W' : Opens X}, W = D s → W' = D (s * t) → ∀ (h : W' ≤ W)
    (x : P.obj (op W)), res P h x = 0 → ∃ N : ℕ, act (t ^ N) W x = 0
  lift : ∀ (s t : R) {W W' : Opens X}, W = D s → W' = D (s * t) → ∀ (h : W' ≤ W)
    (y : P.obj (op W')), ∃ (N : ℕ) (x : P.obj (op W)), res P h x = act (t ^ N) W' y
  D_mul : ∀ s t : R, D (s * t) = D s ⊓ D t
  cover : ∀ (g : R) {ι : Type u} [Fintype ι] (h : ι → R) (N : ℕ), D g ≤ ⨆ i, D (h i) →
    ∃ (L : ℕ) (c : ι → R), g ^ L = ∑ i, c i * h i ^ N

variable {D : R → Opens X} (A : LocalizingAction P D)

namespace LocalizingAction

lemma act_zero (W : Opens X) (x : P.obj (op W)) : A.act 0 W x = 0 := by
  have h := A.act_add 0 0 W x
  rw [add_zero, eq_comm, ← sub_eq_zero, add_sub_cancel_right] at h
  exact h

lemma act_sum {α : Type*} (s : Finset α) (c : α → R) (W : Opens X) (x : P.obj (op W)) :
    A.act (∑ a ∈ s, c a) W x = ∑ a ∈ s, A.act (c a) W x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [A.act_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, A.act_add, ih]

lemma bijective_pow (g : R) (W : Opens X) (hW : W ≤ D g) (L : ℕ) :
    Function.Bijective (A.act (g ^ L) W) := by
  induction L with
  | zero =>
    have : ⇑(A.act (g ^ 0) W) = id := funext fun x => by rw [pow_zero, A.act_one]; rfl
    rw [this]
    exact Function.bijective_id
  | succ L ih =>
    have : ⇑(A.act (g ^ (L + 1)) W) = ⇑(A.act (g ^ L) W) ∘ ⇑(A.act g W) :=
      funext fun x => by rw [pow_succ, A.act_mul]; rfl
    rw [this]
    exact ih.comp (A.bijective g W hW)

end LocalizingAction

variable {ι : Type u} (U : ι → Opens X)

def actC (r : R) (n : ℕ) : Cochain P U n →+ Cochain P U n where
  toFun σ i := A.act r _ (σ i)
  map_zero' := by funext i; exact map_zero _
  map_add' σ τ := by funext i; exact map_add _ _ _

lemma actC_apply (r : R) (n : ℕ) (σ : Cochain P U n) (i : Fin (n + 1) → ι) :
    actC A U r n σ i = A.act r _ (σ i) := rfl

lemma d_actC (r : R) (n : ℕ) (σ : Cochain P U n) :
    d P U n (actC A U r n σ) = actC A U r (n + 1) (d P U n σ) := by
  funext i
  simp only [actC_apply, d_apply, map_sum, map_zsmul, A.res_act]

lemma le_cons {n : ℕ} (j : ι) (I : Fin (n + 1) → ι) :
    inter U (Fin.cons j I : Fin (n + 2) → ι) ≤ inter U I := by
  intro x hx
  rw [mem_inter_iff] at hx ⊢
  intro a
  simpa using hx a.succ

lemma le_cons_comp {n : ℕ} (j : ι) (J : Fin (n + 2) → ι) (k : Fin (n + 2)) :
    inter U (Fin.cons j J : Fin (n + 3) → ι) ≤
      inter U (Fin.cons j (J ∘ k.succAbove) : Fin (n + 2) → ι) := by
  have := inter_le_comp U (Fin.cons j J : Fin (n + 3) → ι) k.succ.succAbove
  rwa [cons_comp_succAbove_succ] at this

variable (h : ι → R)

include A in
lemma inter_eq_prod : ∀ {m : ℕ} (I : Fin (m + 1) → ι), inter (D ∘ h) I = D (∏ a, h (I a))
  | 0, I => by
    rw [Fin.prod_univ_one]
    apply le_antisymm (inter_le _ I 0)
    intro x hx
    rw [mem_inter_iff]
    intro a
    rwa [Fin.fin_one_eq_zero a]
  | m + 1, I => by
    rw [inter_succ, inter_eq_prod (I ∘ Fin.succ), Fin.prod_univ_succ (fun a => h (I a)), A.D_mul]
    rfl

include A in
lemma inter_cons_eq {m : ℕ} (j : ι) (I : Fin (m + 1) → ι) :
    inter (D ∘ h) (Fin.cons j I : Fin (m + 2) → ι) = D ((∏ a, h (I a)) * h j) := by
  rw [inter_eq_prod A h, Fin.prod_univ_succ, mul_comm]
  simp

theorem exists_d_eq_pow_smul [Fintype ι] {n : ℕ} (σ : Cochain P (D ∘ h) (n + 1))
    (hσ : d P (D ∘ h) (n + 1) σ = 0) (j : ι) :
    ∃ (N : ℕ) (τ : Cochain P (D ∘ h) n), d P (D ∘ h) n τ = actC A (D ∘ h) (h j ^ N) (n + 1) σ := by
  classical
  have hlift : ∀ I : Fin (n + 1) → ι, ∃ (N : ℕ) (x : P.obj (op (inter (D ∘ h) I))),
      res P (le_cons _ j I) x = A.act (h j ^ N) _ (σ (Fin.cons j I)) :=
    fun I => A.lift _ (h j) (inter_eq_prod A h I) (inter_cons_eq A h j I) _ _
  choose N x hx using hlift
  obtain ⟨N0, hN0⟩ : ∃ N0, ∀ I, N I ≤ N0 :=
    ⟨Finset.univ.sup N, fun I => Finset.le_sup (Finset.mem_univ I)⟩
  let τ0 : Cochain P (D ∘ h) n := fun I => A.act (h j ^ (N0 - N I)) _ (x I)
  have hτ0 : ∀ I, res P (le_cons _ j I) (τ0 I) = A.act (h j ^ N0) _ (σ (Fin.cons j I)) := by
    intro I
    change res P _ (A.act (h j ^ (N0 - N I)) _ (x I)) = _
    rw [A.res_act, hx, ← A.act_mul, ← pow_add, Nat.sub_add_cancel (hN0 I)]
  have hdef : ∀ J : Fin (n + 2) → ι,
      res P (le_cons _ j J) (d P _ n τ0 J - A.act (h j ^ N0) _ (σ J)) = 0 := by
    intro J
    have hcoc := congrFun hσ (Fin.cons j J)
    rw [d_apply, Fin.sum_univ_succ, Pi.zero_apply] at hcoc
    have e1 : ∀ k : Fin (n + 2), res P (le_cons _ j J) (((-1 : ℤ) ^ (k : ℕ)) •
        res P (inter_le_comp _ J k.succAbove) (τ0 (J ∘ k.succAbove))) =
        ((-1 : ℤ) ^ (k : ℕ)) • A.act (h j ^ N0) _
          (res P (le_cons_comp _ j J k) (σ (Fin.cons j (J ∘ k.succAbove)))) := by
      intro k
      rw [map_zsmul, res_res,
        ← res_res P (le_cons_comp _ j J k) (le_cons _ j (J ∘ k.succAbove)), hτ0, A.res_act]
    have e0 : res P (le_cons _ j J) (σ J) = ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) •
        res P (le_cons_comp _ j J k) (σ (Fin.cons j (J ∘ k.succAbove))) := by
      rw [Fin.val_zero, pow_zero, one_smul,
        res_congr P _ σ (cons_comp_succAbove_zero j J) _ (le_cons _ j J)] at hcoc
      rw [eq_neg_of_add_eq_zero_left hcoc, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Fin.val_succ, pow_succ, mul_neg_one, neg_smul, neg_neg,
        res_congr P _ σ (cons_comp_succAbove_succ j J k) _ (le_cons_comp _ j J k)]
    rw [map_sub, d_apply, map_sum, A.res_act, sub_eq_zero, Finset.sum_congr rfl (fun k _ => e1 k),
      e0, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul]
  have hkill : ∀ J : Fin (n + 2) → ι, ∃ M : ℕ,
      A.act (h j ^ M) _ (d P _ n τ0 J - A.act (h j ^ N0) _ (σ J)) = 0 :=
    fun J => A.kill _ (h j) (inter_eq_prod A h J) (inter_cons_eq A h j J) (le_cons _ j J) _ (hdef J)
  choose M hM using hkill
  obtain ⟨M0, hM0⟩ : ∃ M0, ∀ J, M J ≤ M0 :=
    ⟨Finset.univ.sup M, fun J => Finset.le_sup (Finset.mem_univ J)⟩
  refine ⟨M0 + N0, actC A (D ∘ h) (h j ^ M0) n τ0, ?_⟩
  rw [d_actC]
  funext J
  have hMJ : A.act (h j ^ M0) _ (d P _ n τ0 J - A.act (h j ^ N0) _ (σ J)) = 0 := by
    rw [← Nat.sub_add_cancel (hM0 J), pow_add, A.act_mul, hM J, map_zero]
  rw [map_sub, sub_eq_zero, ← A.act_mul, ← pow_add] at hMJ
  exact hMJ

include A in

theorem cechAcyclic_of_localizingAction [Finite ι] (g : R) (hcov : ⨆ i, D (h i) = D g) :
    CechAcyclic P (D ∘ h) := by
  classical
  have := Fintype.ofFinite ι
  intro n σ hσ
  choose N τ hτ using fun j => exists_d_eq_pow_smul A h σ hσ j
  obtain ⟨N0, hN0⟩ : ∃ N0, ∀ j, N j ≤ N0 :=
    ⟨Finset.univ.sup N, fun j => Finset.le_sup (Finset.mem_univ j)⟩
  obtain ⟨L, c, hc⟩ := A.cover g h N0 hcov.ge
  let T : Cochain P (D ∘ h) n := ∑ j, actC A (D ∘ h) (c j * h j ^ (N0 - N j)) n (τ j)
  have hT : d P _ n T = actC A (D ∘ h) (g ^ L) (n + 1) σ := by
    funext J
    simp only [T, map_sum, d_actC, hτ]
    refine (Finset.sum_apply J _ _).trans ?_
    change ∑ j, A.act _ _ (A.act _ _ (σ J)) = A.act (g ^ L) _ (σ J)
    rw [hc, A.act_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← A.act_mul, mul_assoc, ← pow_add, Nat.sub_add_cancel (hN0 j)]
  have hle : ∀ {m : ℕ} (I : Fin (m + 1) → ι), inter (D ∘ h) I ≤ D g := fun I =>
    (inter_le _ I 0).trans (hcov ▸ le_iSup (fun i => D (h i)) (I 0))
  choose y hy using fun I : Fin (n + 1) → ι => (A.bijective_pow g _ (hle I) L).2 (T I)
  refine ⟨y, funext fun J => (A.bijective_pow g _ (hle J) L).1 ?_⟩
  have e1 : actC A (D ∘ h) (g ^ L) n y = T := funext hy
  have e2 := congrFun (d_actC A (D ∘ h) (g ^ L) n y) J
  rw [e1, hT] at e2
  exact e2.symm

end GroundTheory.Arith.SchemeCoh
