import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.LeviCommutantWordReduction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwLMulSelf

open Finset PositivityTheory.RgBcC.RealD
open GlobalTheory.CompanionTheory.LvChain
open Formalism.REAL (GlRel)

noncomputable section

namespace GlobalTheory.CompanionTheory.LevChainRel

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem units_mul_relation_rearrange_commRing {R : Type*} [Ring R] (c c' a a' d1 d2 : R) (h1 : a * c' = d1 - c' * a)
    (h2 : a' * c = d2 - c * a') (h3 : c' * c = -(c * c')) (h4 : a' * a = -(a * a')) :
    c * a * (c' * a') - c' * a' * (c * a) = c * d1 * a' - c' * d2 * a := by
  have e1 : c * a * (c' * a') = c * (a * c') * a' := by simp only [mul_assoc]
  have e2 : c' * a' * (c * a) = c' * (a' * c) * a := by simp only [mul_assoc]
  have e3 : c' * (c * (a' * a)) = c * (c' * (a * a')) := by
    rw [← mul_assoc, ← mul_assoc c, h3, h4, neg_mul_neg]
  rw [e1, e2, h1, h2]
  simp only [mul_sub, sub_mul, mul_assoc, e3]
  abel

theorem unit_comm (k l k' l' : Lt n) :
    ((creL k * annL l) * (creL k' * annL l') - (creL k' * annL l') * (creL k * annL l) : Module.End ℂ (Cq n V)) =
      (if l = k' then creL k * annL l' else 0) - (if l' = k then creL k' * annL l else 0) := by
  have h1 : (PositivityTheory.RgBcC.RealD.annL l * PositivityTheory.RgBcC.RealD.creL k' : Module.End ℂ (PositivityTheory.RgBcC.RealD.Cq n V)) =
      (if l = k' then 1 else 0) - PositivityTheory.RgBcC.RealD.creL k' * PositivityTheory.RgBcC.RealD.annL l :=
    eq_sub_of_add_eq (GlobalTheory.CompanionTheory.LvChain.annL_creL l k')
  have h2 : (PositivityTheory.RgBcC.RealD.annL l' * PositivityTheory.RgBcC.RealD.creL k : Module.End ℂ (PositivityTheory.RgBcC.RealD.Cq n V)) =
      (if l' = k then 1 else 0) - PositivityTheory.RgBcC.RealD.creL k * PositivityTheory.RgBcC.RealD.annL l' :=
    eq_sub_of_add_eq (GlobalTheory.CompanionTheory.LvChain.annL_creL l' k)
  have h3 : (PositivityTheory.RgBcC.RealD.creL k' * PositivityTheory.RgBcC.RealD.creL k : Module.End ℂ (PositivityTheory.RgBcC.RealD.Cq n V)) =
      -(PositivityTheory.RgBcC.RealD.creL k * PositivityTheory.RgBcC.RealD.creL k') :=
    eq_neg_of_add_eq_zero_left (GlobalTheory.CompanionTheory.LvChain.creL_creL k' k)
  have h4 : (PositivityTheory.RgBcC.RealD.annL l' * PositivityTheory.RgBcC.RealD.annL l : Module.End ℂ (PositivityTheory.RgBcC.RealD.Cq n V)) =
      -(PositivityTheory.RgBcC.RealD.annL l * PositivityTheory.RgBcC.RealD.annL l') :=
    eq_neg_of_add_eq_zero_left (GlobalTheory.CompanionTheory.LvChain.annL_annL l' l)
  rw [GlobalTheory.CompanionTheory.LevChainRel.units_mul_relation_rearrange_commRing _ _ _ _ _ _ h1 h2 h3 h4]
  split_ifs <;> simp

section Abstract

variable {L R : Type*} [Fintype L] [DecidableEq L] [Ring R] [Algebra ℂ R]

def quadA (u : L → L → R) (M : L → L → ℂ) : R := ∑ l : L, ∑ k : L, M l k • u k l

theorem quadA_comm_left (u : L → L → R) (M : L → L → ℂ) (Y : R) :
    quadA u M * Y - Y * quadA u M = ∑ l : L, ∑ k : L, M l k • (u k l * Y - Y * u k l) := by
  simp only [GlobalTheory.CompanionTheory.LevChainRel.quadA, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, smul_sub, Finset.sum_sub_distrib]

theorem quadA_comm_right (u : L → L → R) (N : L → L → ℂ) (X : R) :
    X * quadA u N - quadA u N * X = ∑ l : L, ∑ k : L, N l k • (X * u k l - u k l * X) := by
  simp only [GlobalTheory.CompanionTheory.LevChainRel.quadA, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, smul_sub, Finset.sum_sub_distrib]

theorem quadA_inner (u : L → L → R)
    (hu : ∀ k l k' l', u k l * u k' l' - u k' l' * u k l = (if l = k' then u k l' else 0) - (if l' = k then u k' l else 0))
    (N : L → L → ℂ) (k l : L) :
    u k l * quadA u N - quadA u N * u k l = (∑ l', N l' l • u k l') - ∑ k', N k k' • u k' l := by
  rw [GlobalTheory.CompanionTheory.LevChainRel.quadA_comm_right]
  simp only [hu, smul_sub, Finset.sum_sub_distrib, smul_ite, smul_zero]
  refine congrArg₂ _ ?_ ?_
  · simp
  · rw [Finset.sum_comm]
    simp

theorem triple_sum_reindex_matrix_mul (u : L → L → R) (M N : L → L → ℂ) :
    ∑ l, ∑ k, ∑ l', (M l k * N l' l) • u k l' = ∑ l', ∑ k, ∑ j, (N l' j * M j k) • u k l' := by
  calc ∑ l, ∑ k, ∑ l', (M l k * N l' l) • u k l'
        = ∑ l, ∑ l', ∑ k, (M l k * N l' l) • u k l' :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ l', ∑ l, ∑ k, (M l k * N l' l) • u k l' := Finset.sum_comm
    _ = ∑ l', ∑ k, ∑ l, (M l k * N l' l) • u k l' :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ l', ∑ k, ∑ j, (N l' j * M j k) • u k l' :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
            Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

theorem quadA_comm (u : L → L → R)
    (hu : ∀ k l k' l', u k l * u k' l' - u k' l' * u k l = (if l = k' then u k l' else 0) - (if l' = k then u k' l else 0))
    (M N : L → L → ℂ) :
    quadA u M * quadA u N - quadA u N * quadA u M =
      quadA u (fun l k => ∑ j, N l j * M j k - ∑ j, M l j * N j k) := by
  rw [GlobalTheory.CompanionTheory.LevChainRel.quadA_comm_left]
  simp only [GlobalTheory.CompanionTheory.LevChainRel.quadA_inner u hu]
  simp only [GlobalTheory.CompanionTheory.LevChainRel.quadA, smul_sub, sub_smul, Finset.smul_sum,
    Finset.sum_smul, smul_smul, Finset.sum_sub_distrib]
  refine congrArg₂ _ (GlobalTheory.CompanionTheory.LevChainRel.triple_sum_reindex_matrix_mul u M N) ?_
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

end Abstract

section Matrix

def adG (s : Bool) (p q : Fin n) (u : Bool) (x y : Fin n) (k : Lt n) : ℂ :=
  (if q = x ∧ k.1 = xor s u ∧ k.2.1 = (p, y) then 1 else 0) -
    (if y = p ∧ k.1 = xor s u ∧ k.2.1 = (x, q) then 1 else 0)

def Mx (lev : Fin n → ℕ) (s : Bool) (p q : Fin n) (l k : Lt n) : ℂ :=
  if inUU lev l then adCL s p q l k else 0

theorem pick (σ : Bool) (x y : Fin n) (h : x < y) (G : Bool → Fin n → Fin n → ℂ) :
    ∑ j : Lt n, (if j.1 = σ ∧ j.2.1 = (x, y) then (1 : ℂ) else 0) * G j.1 j.2.1.1 j.2.1.2 = G σ x y := by
  rw [Finset.sum_eq_single (σ, (⟨(x, y), h⟩ : {p : Fin n × Fin n // p.1 < p.2}))]
  · simp
  · intro b _ hb
    rw [if_neg, zero_mul]
    rintro ⟨h1, h2⟩
    exact hb (Prod.ext h1 (Subtype.ext h2))
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

theorem lt_of_lev {lev : Fin n → ℕ} (hm : Monotone lev) {x y : Fin n} (h : lev x < lev y) : x < y := by
  by_contra hxy
  exact absurd (hm (not_lt.mp hxy)) (not_le.mpr h)

theorem sum_adCL {lev : Fin n → ℕ} (hm : Monotone lev) (s : Bool) {p q : Fin n} (hpq : lev p = lev q) (l : Lt n)
    (hl : inUU lev l) (G : Bool → Fin n → Fin n → ℂ) :
    ∑ j : Lt n, adCL s p q l j * G j.1 j.2.1.1 j.2.1.2 =
      (if q = l.2.1.1 then G (xor s l.1) p l.2.1.2 else 0) -
        (if l.2.1.2 = p then G (xor s l.1) l.2.1.1 q else 0) := by
  unfold PositivityTheory.RgBcC.RealD.adCL
  simp only [sub_mul, Finset.sum_sub_distrib]
  refine congrArg₂ _ ?_ ?_
  · by_cases hq : q = l.2.1.1
    · have hlt : p < l.2.1.2 := GlobalTheory.CompanionTheory.LevChainRel.lt_of_lev hm (by rw [hpq, hq]; exact hl)
      simp only [hq, eq_self_iff_true, true_and, if_true]
      exact GlobalTheory.CompanionTheory.LevChainRel.pick _ _ _ hlt G
    · simp [hq]
  · by_cases hp : l.2.1.2 = p
    · have hlt : l.2.1.1 < q := GlobalTheory.CompanionTheory.LevChainRel.lt_of_lev hm (by rw [← hpq, ← hp]; exact hl)
      simp only [hp, eq_self_iff_true, true_and, if_true]
      exact GlobalTheory.CompanionTheory.LevChainRel.pick _ _ _ hlt G
    · simp [hp]

theorem sum_Mx {lev : Fin n → ℕ} (hm : Monotone lev) (s t : Bool) {a b c d : Fin n} (hab : lev a = lev b)
    (hcd : lev c = lev d) (l k : Lt n) (hl : inUU lev l) :
    ∑ j : Lt n, Mx lev t c d l j * Mx lev s a b j k =
      (if d = l.2.1.1 then adG s a b (xor t l.1) c l.2.1.2 k else 0) -
        (if l.2.1.2 = c then adG s a b (xor t l.1) l.2.1.1 d k else 0) := by
  have key : ∀ j : PositivityTheory.RgBcC.RealD.Lt n,
      GlobalTheory.CompanionTheory.LevChainRel.Mx lev t c d l j * GlobalTheory.CompanionTheory.LevChainRel.Mx lev s a b j k =
        PositivityTheory.RgBcC.RealD.adCL t c d l j *
          (if lev j.2.1.1 < lev j.2.1.2 then GlobalTheory.CompanionTheory.LevChainRel.adG s a b j.1 j.2.1.1 j.2.1.2 k else 0) := by
    intro j
    unfold GlobalTheory.CompanionTheory.LevChainRel.Mx
    rw [if_pos hl]
    by_cases hj : PositivityTheory.RgBcC.RealD.inUU lev j
    · have hj' : lev j.2.1.1 < lev j.2.1.2 := hj
      rw [if_pos hj, if_pos hj']
      rfl
    · have hj' : ¬ lev j.2.1.1 < lev j.2.1.2 := hj
      rw [if_neg hj, if_neg hj']
  refine (Finset.sum_congr rfl fun j _ => key j).trans
    ((GlobalTheory.CompanionTheory.LevChainRel.sum_adCL hm t hcd l hl
      (fun σ x y => if lev x < lev y then GlobalTheory.CompanionTheory.LevChainRel.adG s a b σ x y k else 0)).trans ?_)
  refine congrArg₂ _ ?_ ?_
  · by_cases hd : d = l.2.1.1
    · have hlt : lev c < lev l.2.1.2 := by rw [hcd, hd]; exact hl
      rw [if_pos hd, if_pos hd, if_pos hlt]
    · rw [if_neg hd, if_neg hd]
  · by_cases hc : l.2.1.2 = c
    · have hlt : lev l.2.1.1 < lev d := by rw [← hcd, ← hc]; exact hl
      rw [if_pos hc, if_pos hc, if_pos hlt]
    · rw [if_neg hc, if_neg hc]

theorem ind3 (P Q R : Prop) [Decidable P] [Decidable Q] [Decidable R] :
    (if P ∧ Q ∧ R then (1 : ℂ) else 0) =
      (if P then 1 else 0) * (if Q then 1 else 0) * (if R then 1 else 0) := by
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;> simp [hP, hQ, hR]

theorem ite_zero_eq (P : Prop) [Decidable P] (X : ℂ) : (if P then X else 0) = (if P then 1 else 0) * X := by
  by_cases hP : P <;> simp [hP]

theorem key_id (s t u : Bool) (a b c d x y : Fin n) (k : Lt n) :
    ((if d = x then adG s a b (xor t u) c y k else 0) - (if y = c then adG s a b (xor t u) x d k else 0)) -
      ((if b = x then adG t c d (xor s u) a y k else 0) - (if y = a then adG t c d (xor s u) x b k else 0)) =
    (if b = c then adG (xor s t) a d u x y k else 0) - (if d = a then adG (xor s t) c b u x y k else 0) := by
  have hx1 : xor t (xor s u) = xor s (xor t u) := by cases s <;> cases t <;> cases u <;> rfl
  have hx2 : xor (xor s t) u = xor s (xor t u) := by cases s <;> cases t <;> cases u <;> rfl
  rw [GlobalTheory.CompanionTheory.LevChainRel.ite_zero_eq (d = x), GlobalTheory.CompanionTheory.LevChainRel.ite_zero_eq (y = c),
    GlobalTheory.CompanionTheory.LevChainRel.ite_zero_eq (b = x), GlobalTheory.CompanionTheory.LevChainRel.ite_zero_eq (y = a),
    GlobalTheory.CompanionTheory.LevChainRel.ite_zero_eq (b = c), GlobalTheory.CompanionTheory.LevChainRel.ite_zero_eq (d = a)]
  unfold GlobalTheory.CompanionTheory.LevChainRel.adG
  rw [hx1, hx2]
  simp only [GlobalTheory.CompanionTheory.LevChainRel.ind3]
  ring

theorem mx_id {lev : Fin n → ℕ} (hm : Monotone lev) (s t : Bool) {a b c d : Fin n} (hab : lev a = lev b)
    (hcd : lev c = lev d) (l k : Lt n) :
    ∑ j, Mx lev t c d l j * Mx lev s a b j k - ∑ j, Mx lev s a b l j * Mx lev t c d j k =
      (if b = c then Mx lev (xor s t) a d l k else 0) - (if d = a then Mx lev (xor s t) c b l k else 0) := by
  by_cases hl : PositivityTheory.RgBcC.RealD.inUU lev l
  · rw [GlobalTheory.CompanionTheory.LevChainRel.sum_Mx hm s t hab hcd l k hl,
      GlobalTheory.CompanionTheory.LevChainRel.sum_Mx hm t s hcd hab l k hl,
      GlobalTheory.CompanionTheory.LevChainRel.key_id]
    simp only [GlobalTheory.CompanionTheory.LevChainRel.Mx, if_pos hl]
    rfl
  · simp [GlobalTheory.CompanionTheory.LevChainRel.Mx, hl]

end Matrix

section Ops

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem adLL_eq (lev : Fin n → ℕ) (s : Bool) (p q : Fin n) :
    (adLL lev s p q : Module.End ℂ (Cq n V)) =
      quadA (fun k l => (creL k * annL l : Module.End ℂ (Cq n V))) (Mx lev s p q) := by
  simp only [PositivityTheory.RgBcC.RealD.adLL, GlobalTheory.CompanionTheory.LevChainRel.quadA,
    GlobalTheory.CompanionTheory.LevChainRel.Mx, ite_smul, zero_smul]

theorem adLL_comm {lev : Fin n → ℕ} (hm : Monotone lev) (s t : Bool) {a b c d : Fin n} (hab : lev a = lev b)
    (hcd : lev c = lev d) :
    (adLL lev s a b * adLL lev t c d - adLL lev t c d * adLL lev s a b : Module.End ℂ (Cq n V)) =
      (if b = c then adLL lev (xor s t) a d else 0) - (if d = a then adLL lev (xor s t) c b else 0) := by
  simp only [GlobalTheory.CompanionTheory.LevChainRel.adLL_eq (V := V)]
  rw [GlobalTheory.CompanionTheory.LevChainRel.quadA_comm
    (fun k l => (PositivityTheory.RgBcC.RealD.creL k * PositivityTheory.RgBcC.RealD.annL l : Module.End ℂ (PositivityTheory.RgBcC.RealD.Cq n V)))
    (fun k l k' l' => GlobalTheory.CompanionTheory.LevChainRel.unit_comm k l k' l')]
  simp only [GlobalTheory.CompanionTheory.LevChainRel.mx_id hm s t hab hcd]
  by_cases hbc : b = c <;> by_cases hda : d = a <;>
    simp [hbc, hda, GlobalTheory.CompanionTheory.LevChainRel.quadA, sub_smul, Finset.sum_sub_distrib]

theorem liftL_mul (A B : Module.End ℂ V) :
    (liftL n (A * B) : Module.End ℂ (Cq n V)) = (liftL n A : Module.End ℂ (Cq n V)) * liftL n B := rfl

theorem liftL_sub (A B : Module.End ℂ V) :
    (liftL n (A - B) : Module.End ℂ (Cq n V)) = (liftL n A : Module.End ℂ (Cq n V)) - liftL n B :=
  LinearMap.ext fun _ => rfl

theorem liftL_zero : (liftL n (0 : Module.End ℂ V) : Module.End ℂ (Cq n V)) = 0 :=
  LinearMap.ext fun _ => rfl

theorem liftL_commute_adLL (T : Module.End ℂ V) (lev : Fin n → ℕ) (s : Bool) (p q : Fin n) :
    Commute (liftL n T : Module.End ℂ (Cq n V)) (adLL lev s p q) := by
  unfold PositivityTheory.RgBcC.RealD.adLL
  refine Commute.sum_right _ _ _ fun l _ => Commute.sum_right _ _ _ fun k _ => ?_
  split_ifs
  · have h1 : Commute (PositivityTheory.RgBcC.RealD.liftL n T : Module.End ℂ (PositivityTheory.RgBcC.RealD.Cq n V)) (PositivityTheory.RgBcC.RealD.creL k) :=
      GlobalTheory.CompanionTheory.LvChain.liftL_creL T k
    have h2 : Commute (PositivityTheory.RgBcC.RealD.liftL n T : Module.End ℂ (PositivityTheory.RgBcC.RealD.Cq n V)) (PositivityTheory.RgBcC.RealD.annL l) :=
      GlobalTheory.CompanionTheory.LvChain.liftL_annL T l
    exact (h1.mul_right h2).smul_right _
  · exact Commute.zero_right _

def xS (E1 E2 : Fin n → Fin n → Module.End ℂ V) (s : Bool) (p q : Fin n) : Module.End ℂ V :=
  if s then pA E1 E2 p q else kA E1 E2 p q

def Tc (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (s : Bool) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  (liftL n (xS E1 E2 s p q) : Module.End ℂ (Cq n V)) + adLL lev s p q

theorem comm_kk {R : Type*} [Ring R] {A B C D : R} (h : A * D = D * A) (h' : C * B = B * C) :
    (A + B) * (C + D) - (C + D) * (A + B) = (A * C - C * A) + (B * D - D * B) := by
  simp only [add_mul, mul_add]
  rw [h, h']
  abel

theorem comm_kp {R : Type*} [Ring R] {A B C D : R} (h : A * D = D * A) (h' : C * B = B * C) :
    (A + B) * (C - D) - (C - D) * (A + B) = (A * C - C * A) - (B * D - D * B) := by
  simp only [add_mul, mul_add, mul_sub, sub_mul]
  rw [h, h']
  abel

theorem comm_pk {R : Type*} [Ring R] {A B C D : R} (h : A * D = D * A) (h' : C * B = B * C) :
    (A - B) * (C + D) - (C + D) * (A - B) = (A * C - C * A) - (B * D - D * B) := by
  simp only [add_mul, mul_add, mul_sub, sub_mul]
  rw [h, h']
  abel

theorem comm_pp {R : Type*} [Ring R] {A B C D : R} (h : A * D = D * A) (h' : C * B = B * C) :
    (A - B) * (C - D) - (C - D) * (A - B) = (A * C - C * A) + (B * D - D * B) := by
  simp only [mul_sub, sub_mul]
  rw [h, h']
  abel

theorem xS_comm {E1 E2 : Fin n → Fin n → Module.End ℂ V} (h : IsPairA E1 E2) (s t : Bool) (a b c d : Fin n) :
    xS E1 E2 s a b * xS E1 E2 t c d - xS E1 E2 t c d * xS E1 E2 s a b =
      (if b = c then xS E1 E2 (xor s t) a d else 0) - (if d = a then xS E1 E2 (xor s t) c b else 0) := by
  obtain ⟨h1, h2, h12⟩ := h
  have e1 : E1 a b * E1 c d - E1 c d * E1 a b =
      (if b = c then E1 a d else 0) - (if d = a then E1 c b else 0) := h1 a b c d
  have e2 : E2 a b * E2 c d - E2 c d * E2 a b =
      (if b = c then E2 a d else 0) - (if d = a then E2 c b else 0) := h2 a b c d
  cases s <;> cases t <;>
    simp only [GlobalTheory.CompanionTheory.LevChainRel.xS, PositivityTheory.RgBcC.RealD.kA, PositivityTheory.RgBcC.RealD.pA,
      Bool.false_eq_true, eq_self_iff_true, if_true, if_false, Bool.false_xor, Bool.true_xor,
      Bool.not_true, Bool.not_false]
  · rw [GlobalTheory.CompanionTheory.LevChainRel.comm_kk (h12 a b c d) (h12 c d a b), e1, e2]
    split_ifs <;> abel
  · rw [GlobalTheory.CompanionTheory.LevChainRel.comm_kp (h12 a b c d) (h12 c d a b), e1, e2]
    split_ifs <;> abel
  · rw [GlobalTheory.CompanionTheory.LevChainRel.comm_pk (h12 a b c d) (h12 c d a b), e1, e2]
    split_ifs <;> abel
  · rw [GlobalTheory.CompanionTheory.LevChainRel.comm_pp (h12 a b c d) (h12 c d a b), e1, e2]
    split_ifs <;> abel

theorem Tc_comm {lev : Fin n → ℕ} (hm : Monotone lev) {E1 E2 : Fin n → Fin n → Module.End ℂ V} (h : IsPairA E1 E2)
    (s t : Bool) {a b c d : Fin n} (hab : lev a = lev b) (hcd : lev c = lev d) :
    Tc lev E1 E2 s a b * Tc lev E1 E2 t c d - Tc lev E1 E2 t c d * Tc lev E1 E2 s a b =
      (if b = c then Tc lev E1 E2 (xor s t) a d else 0) - (if d = a then Tc lev E1 E2 (xor s t) c b else 0) := by
  unfold GlobalTheory.CompanionTheory.LevChainRel.Tc
  rw [GlobalTheory.CompanionTheory.LevChainRel.comm_kk
      (GlobalTheory.CompanionTheory.LevChainRel.liftL_commute_adLL (GlobalTheory.CompanionTheory.LevChainRel.xS E1 E2 s a b) lev t c d).eq
      (GlobalTheory.CompanionTheory.LevChainRel.liftL_commute_adLL (GlobalTheory.CompanionTheory.LevChainRel.xS E1 E2 t c d) lev s a b).eq,
    ← GlobalTheory.CompanionTheory.LevChainRel.liftL_mul, ← GlobalTheory.CompanionTheory.LevChainRel.liftL_mul, ← GlobalTheory.CompanionTheory.LevChainRel.liftL_sub,
    GlobalTheory.CompanionTheory.LevChainRel.xS_comm h, GlobalTheory.CompanionTheory.LevChainRel.adLL_comm hm s t hab hcd,
    GlobalTheory.CompanionTheory.LevChainRel.liftL_sub]
  split_ifs <;> (try rw [GlobalTheory.CompanionTheory.LevChainRel.liftL_zero]) <;> abel

end Ops

section Final

theorem half_sum_bracket_half_sum {R : Type*} [Ring R] [Algebra ℂ R] {A B C D U W : R} (h1 : A * C - C * A = U)
    (h2 : A * D - D * A = W) (h3 : B * C - C * B = W) (h4 : B * D - D * B = U) :
    ((1 / 2 : ℂ) • (A + B)) * ((1 / 2 : ℂ) • (C + D)) - ((1 / 2 : ℂ) • (C + D)) * ((1 / 2 : ℂ) • (A + B)) =
      (1 / 2 : ℂ) • (U + W) := by
  rw [smul_mul_smul_comm, smul_mul_smul_comm, ← smul_sub]
  have e : (A + B) * (C + D) - (C + D) * (A + B) =
      (A * C - C * A) + (A * D - D * A) + (B * C - C * B) + (B * D - D * B) := by
    simp only [add_mul, mul_add]
    abel
  rw [e, h1, h2, h3, h4, show U + W + W + U = (2 : ℂ) • (U + W) by rw [two_smul]; abel, smul_smul]
  congr 1
  norm_num

theorem half_diff_bracket_half_diff {R : Type*} [Ring R] [Algebra ℂ R] {A B C D U W : R} (h1 : A * C - C * A = U)
    (h2 : A * D - D * A = W) (h3 : B * C - C * B = W) (h4 : B * D - D * B = U) :
    ((1 / 2 : ℂ) • (A - B)) * ((1 / 2 : ℂ) • (C - D)) - ((1 / 2 : ℂ) • (C - D)) * ((1 / 2 : ℂ) • (A - B)) =
      (1 / 2 : ℂ) • (U - W) := by
  rw [smul_mul_smul_comm, smul_mul_smul_comm, ← smul_sub]
  have e : (A - B) * (C - D) - (C - D) * (A - B) =
      (A * C - C * A) - (A * D - D * A) - (B * C - C * B) + (B * D - D * B) := by
    simp only [sub_mul, mul_sub]
    abel
  rw [e, h1, h2, h3, h4, show U - W - W + U = (2 : ℂ) • (U - W) by rw [two_smul]; abel, smul_smul]
  congr 1
  norm_num

theorem half_sum_commute_half_diff {R : Type*} [Ring R] [Algebra ℂ R] {A B C D U W : R} (h1 : A * C - C * A = U)
    (h2 : A * D - D * A = W) (h3 : B * C - C * B = W) (h4 : B * D - D * B = U) :
    ((1 / 2 : ℂ) • (A + B)) * ((1 / 2 : ℂ) • (C - D)) = ((1 / 2 : ℂ) • (C - D)) * ((1 / 2 : ℂ) • (A + B)) := by
  rw [smul_mul_smul_comm, smul_mul_smul_comm, ← sub_eq_zero, ← smul_sub]
  have e : (A + B) * (C - D) - (C - D) * (A + B) =
      (A * C - C * A) - (A * D - D * A) + (B * C - C * B) - (B * D - D * B) := by
    simp only [add_mul, mul_add, sub_mul, mul_sub]
    abel
  rw [e, h1, h2, h3, h4]
  simp

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem evLc_letter {lev : Fin n → ℕ} (E1 E2 : Fin n → Fin n → Module.End ℂ V) (s : Bool) {p q : Fin n}
    (h : lev p = lev q) : evLc lev E1 E2 (FreeAlgebra.ι ℂ (s, p, q)) = Tc lev E1 E2 s p q := by
  simp only [PositivityTheory.RgBcC.RealD.evLc, FreeAlgebra.lift_ι_apply]
  rw [if_pos h]
  rfl

theorem leviFamilyOne_eq_half_sum {lev : Fin n → ℕ} (E1 E2 : Fin n → Fin n → Module.End ℂ V) {p q : Fin n} (h : lev p = lev q) :
    firstLeviFamily lev E1 E2 p q = (1 / 2 : ℂ) • (Tc lev E1 E2 false p q + Tc lev E1 E2 true p q) := by
  unfold PositivityTheory.RgBcC.RealD.firstLeviFamily
  rw [GlobalTheory.CompanionTheory.LevChainRel.evLc_letter E1 E2 false h,
    GlobalTheory.CompanionTheory.LevChainRel.evLc_letter E1 E2 true h]

theorem leviFamilyTwo_eq_half_diff {lev : Fin n → ℕ} (E1 E2 : Fin n → Fin n → Module.End ℂ V) {p q : Fin n} (h : lev p = lev q) :
    secondLeviFamily lev E1 E2 p q = (1 / 2 : ℂ) • (Tc lev E1 E2 false p q - Tc lev E1 E2 true p q) := by
  unfold PositivityTheory.RgBcC.RealD.secondLeviFamily
  rw [GlobalTheory.CompanionTheory.LevChainRel.evLc_letter E1 E2 false h,
    GlobalTheory.CompanionTheory.LevChainRel.evLc_letter E1 E2 true h]

theorem levRel : LevRel := by
  intro n lev hm V _ _ E1 E2 h a b c d hab hcd
  have key : ∀ s t : Bool,
      GlobalTheory.CompanionTheory.LevChainRel.Tc lev E1 E2 s a b * GlobalTheory.CompanionTheory.LevChainRel.Tc lev E1 E2 t c d -
                   GlobalTheory.CompanionTheory.LevChainRel.Tc lev E1 E2 t c d * GlobalTheory.CompanionTheory.LevChainRel.Tc lev E1 E2 s a b =
        (if b = c then GlobalTheory.CompanionTheory.LevChainRel.Tc lev E1 E2 (xor s t) a d else 0) -
          (if d = a then GlobalTheory.CompanionTheory.LevChainRel.Tc lev E1 E2 (xor s t) c b else 0) :=
    fun s t => GlobalTheory.CompanionTheory.LevChainRel.Tc_comm hm h s t hab hcd
  have h1 := key false false
  have h2 := key false true
  have h3 := key true false
  have h4 := key true true
  simp only [Bool.false_xor, Bool.true_xor, Bool.not_true, Bool.not_false] at h1 h2 h3 h4
  refine ⟨?_, ?_, ?_⟩
  · rw [GlobalTheory.CompanionTheory.LevChainRel.leviFamilyOne_eq_half_sum E1 E2 hab, GlobalTheory.CompanionTheory.LevChainRel.leviFamilyOne_eq_half_sum E1 E2 hcd,
      GlobalTheory.CompanionTheory.LevChainRel.half_sum_bracket_half_sum h1 h2 h3 h4]
    split_ifs with hbc hda hda
    · rw [GlobalTheory.CompanionTheory.LevChainRel.leviFamilyOne_eq_half_sum E1 E2 (show lev a = lev d by rw [hab, hbc, hcd]),
        GlobalTheory.CompanionTheory.LevChainRel.leviFamilyOne_eq_half_sum E1 E2 (show lev c = lev b by rw [hcd, hda, hab])]
      simp only [smul_add, smul_sub, smul_zero]
      abel
    · rw [GlobalTheory.CompanionTheory.LevChainRel.leviFamilyOne_eq_half_sum E1 E2 (show lev a = lev d by rw [hab, hbc, hcd])]
      simp only [smul_add, smul_sub, smul_zero]
      abel
    · rw [GlobalTheory.CompanionTheory.LevChainRel.leviFamilyOne_eq_half_sum E1 E2 (show lev c = lev b by rw [hcd, hda, hab])]
      simp only [smul_add, smul_sub, smul_zero]
      abel
    · simp only [smul_add, smul_sub, smul_zero]
      abel
  · rw [GlobalTheory.CompanionTheory.LevChainRel.leviFamilyTwo_eq_half_diff E1 E2 hab, GlobalTheory.CompanionTheory.LevChainRel.leviFamilyTwo_eq_half_diff E1 E2 hcd,
      GlobalTheory.CompanionTheory.LevChainRel.half_diff_bracket_half_diff h1 h2 h3 h4]
    split_ifs with hbc hda hda
    · rw [GlobalTheory.CompanionTheory.LevChainRel.leviFamilyTwo_eq_half_diff E1 E2 (show lev a = lev d by rw [hab, hbc, hcd]),
        GlobalTheory.CompanionTheory.LevChainRel.leviFamilyTwo_eq_half_diff E1 E2 (show lev c = lev b by rw [hcd, hda, hab])]
      simp only [smul_add, smul_sub, smul_zero]
      abel
    · rw [GlobalTheory.CompanionTheory.LevChainRel.leviFamilyTwo_eq_half_diff E1 E2 (show lev a = lev d by rw [hab, hbc, hcd])]
      simp only [smul_add, smul_sub, smul_zero]
      abel
    · rw [GlobalTheory.CompanionTheory.LevChainRel.leviFamilyTwo_eq_half_diff E1 E2 (show lev c = lev b by rw [hcd, hda, hab])]
      simp only [smul_add, smul_sub, smul_zero]
      abel
    · simp only [smul_add, smul_sub, smul_zero]
      abel
  · rw [GlobalTheory.CompanionTheory.LevChainRel.leviFamilyOne_eq_half_sum E1 E2 hab, GlobalTheory.CompanionTheory.LevChainRel.leviFamilyTwo_eq_half_diff E1 E2 hcd]
    exact GlobalTheory.CompanionTheory.LevChainRel.half_sum_commute_half_diff h1 h2 h3 h4

end Final

end GlobalTheory.CompanionTheory.LevChainRel
