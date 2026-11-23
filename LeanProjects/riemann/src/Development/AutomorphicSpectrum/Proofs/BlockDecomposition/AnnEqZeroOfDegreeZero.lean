import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveWedgeHighestCoefficient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SgMulSelf

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.PairMult.COU

open GlobalTheory.CompanionTheory.PairMult
open GlobalTheory.CompanionTheory.RealMult (cp)
open GlobalTheory.CompanionTheory.RealMult.BdSqProof (d_sq sum_cp cp_jacobi)
open CompanionTheory.D.LK (Pos key)
open Formalism.REAL (GlRel)

variable {n : ℕ}

theorem keyL_inj {i j : Lt n} (h : keyL i = keyL j) : i = j := by
  obtain ⟨s, p⟩ := i
  obtain ⟨t, q⟩ := j
  have hp := GlobalTheory.CompanionTheory.RealMult.BdSqProof.key_lt p
  have hq := GlobalTheory.CompanionTheory.RealMult.BdSqProof.key_lt q
  have hk : key p = key q → p = q := fun e => CompanionTheory.D.LK.Car.key_inj e
  have hn : n * n < (n + 1) * (n + 1) := by nlinarith
  cases s <;> cases t <;> simp only [keyL, Bool.false_eq_true, if_false, if_true] at h
  · rw [hk (by omega)]
  · omega
  · omega
  · rw [hk (by omega)]

section Basic
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem ann_apply (i : Lt n) (x : Cq n V) (A : Finset (Lt n)) :
    annq i x A = if i ∈ A then 0 else sgL i A • x (insert i A) := rfl

theorem cre_apply (i : Lt n) (x : Cq n V) (A : Finset (Lt n)) :
    creq i x A = if i ∈ A then sgL i A • x (A.erase i) else 0 := rfl

theorem lift_apply (T : V →ₗ[ℂ] W) (x : Cq n V) (A : Finset (Lt n)) : liftq n T x A = T (x A) := rfl

end Basic

section Car

def tw (i j : Lt n) : ℂ := if keyL j < keyL i then -1 else 1

theorem tw_self (i : Lt n) : tw i i = 1 := by simp [tw]

theorem tw_mul_self (i j : Lt n) : tw i j * tw i j = 1 := by
  unfold tw; split_ifs <;> simp

theorem tw_swap {i j : Lt n} (h : i ≠ j) : tw j i = -tw i j := by
  have hk : keyL i ≠ keyL j := fun e => h (keyL_inj e)
  unfold tw
  rcases lt_or_gt_of_ne hk with h1 | h1
  · simp [h1, h1.not_gt]
  · simp [h1, h1.not_gt]

theorem sg_mul_self (i : Lt n) (A : Finset (Lt n)) : sgL i A * sgL i A = 1 := by
  unfold sgL
  rw [← mul_pow]; simp

theorem sg_insert (i : Lt n) {j : Lt n} {A : Finset (Lt n)} (h : j ∉ A) :
    sgL i (insert j A) = tw i j * sgL i A := by
  unfold sgL tw
  rw [Finset.filter_insert]
  split_ifs with hk
  · rw [Finset.card_insert_of_notMem (fun hm => h (Finset.mem_filter.1 hm).1), pow_succ]; ring
  · simp

theorem sg_erase (i : Lt n) {j : Lt n} {A : Finset (Lt n)} (h : j ∈ A) :
    sgL i (A.erase j) = tw i j * sgL i A := by
  have h1 := sg_insert i (Finset.notMem_erase j A)
  rw [Finset.insert_erase h] at h1
  rw [h1, ← mul_assoc, tw_mul_self, one_mul]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem ann_ann (i j : Lt n) : (annq i * annq j + annq j * annq i : Module.End ℂ (Cq n V)) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, LinearMap.zero_apply, Pi.zero_apply,
    ann_apply]
  by_cases hij : i = j
  · subst hij
    simp
  have hji : j ≠ i := fun e => hij e.symm
  by_cases hi : i ∈ A
  · simp [hi]
  by_cases hj : j ∈ A
  · simp [hj]
  simp only [hi, hj, Finset.mem_insert, hij, hji, or_self, if_false]
  rw [sg_insert j hi, sg_insert i hj, tw_swap hij, Finset.insert_comm j i, smul_smul, smul_smul, ← add_smul]
  have : sgL i A * (-tw i j * sgL j A) + sgL j A * (tw i j * sgL i A) = 0 := by ring
  rw [this, zero_smul]

theorem cre_cre (i j : Lt n) : (creq i * creq j + creq j * creq i : Module.End ℂ (Cq n V)) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, LinearMap.zero_apply, Pi.zero_apply,
    cre_apply]
  by_cases hij : i = j
  · subst hij
    simp
  have hji : j ≠ i := fun e => hij e.symm
  by_cases hi : i ∈ A
  swap
  · simp [hi]
  by_cases hj : j ∈ A
  swap
  · simp [hj]
  simp only [hi, hj, Finset.mem_erase, ne_eq, hij, hji, not_false_eq_true, and_self, if_true]
  rw [sg_erase j hi, sg_erase i hj, tw_swap hij, Finset.erase_right_comm (a := j) (b := i), smul_smul, smul_smul,
    ← add_smul]
  have : sgL i A * (-tw i j * sgL j A) + sgL j A * (tw i j * sgL i A) = 0 := by ring
  rw [this, zero_smul]

theorem ann_cre (i j : Lt n) :
    (annq i * creq j + creq j * annq i : Module.End ℂ (Cq n V)) = if i = j then 1 else 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, ann_apply, cre_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i ∈ A
    · simp [hi, sg_erase i hi, tw_self, smul_smul, sg_mul_self, Finset.insert_erase hi]
    · simp [hi, sg_insert i hi, tw_self, smul_smul, sg_mul_self, Finset.erase_insert hi]
  have hji : j ≠ i := fun e => hij e.symm
  rw [if_neg hij, LinearMap.zero_apply, Pi.zero_apply]
  by_cases hi : i ∈ A
  · simp [hi, hij]
  by_cases hj : j ∈ A
  swap
  · simp [hj, hji]
  simp only [hi, hj, Finset.mem_insert, Finset.mem_erase, or_true, and_false, if_true, if_false]
  rw [sg_insert j hi, sg_erase i hj, tw_swap hij, Finset.erase_insert_of_ne hij, smul_smul, smul_smul,
    ← add_smul]
  have : sgL i A * (-tw i j * sgL j A) + sgL j A * (tw i j * sgL i A) = 0 := by ring
  rw [this, zero_smul]

theorem lift_ann (T : Module.End ℂ V) (i : Lt n) :
    Commute (liftq n T : Module.End ℂ (Cq n V)) (annq i) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [Module.End.mul_apply, lift_apply, ann_apply]
  split_ifs <;> simp

theorem lift_cre (T : Module.End ℂ V) (i : Lt n) :
    Commute (liftq n T : Module.End ℂ (Cq n V)) (creq i) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [Module.End.mul_apply, lift_apply, cre_apply]
  split_ifs <;> simp

end Car

section Constants

def cq (i j k : Lt n) : ℂ := if k.1 = (i.1 == j.1) then cp i.2 j.2 k.2 else 0

theorem cq_anti (i j k : Lt n) : cq i j k = -cq j i k := by
  have e : (j.1 == i.1) = (i.1 == j.1) := by cases i.1 <;> cases j.1 <;> rfl
  simp only [cq, cp, e]
  split_ifs <;> simp

theorem sum_cq (p q r k : Lt n) : ∑ i, cq p q i * cq i r k =
    if k.1 = ((p.1 == q.1) == r.1) then ∑ m, cp p.2 q.2 m * cp m r.2 k.2 else 0 := by
  obtain ⟨s, p⟩ := p
  obtain ⟨t, q⟩ := q
  obtain ⟨u, r⟩ := r
  obtain ⟨w, k⟩ := k
  rw [Fintype.sum_prod_type]
  cases s <;> cases t <;> cases u <;> cases w <;> simp [cq]

theorem cq_jacobi (p q r k : Lt n) :
    ∑ i, cq p q i * cq i r k + ∑ i, cq q r i * cq i p k + ∑ i, cq r p i * cq i q k = 0 := by
  rw [sum_cq, sum_cq, sum_cq]
  have h1 : ((q.1 == r.1) == p.1) = ((p.1 == q.1) == r.1) := by cases p.1 <;> cases q.1 <;> cases r.1 <;> rfl
  have h2 : ((r.1 == p.1) == q.1) = ((p.1 == q.1) == r.1) := by cases p.1 <;> cases q.1 <;> cases r.1 <;> rfl
  rw [h1, h2]
  split_ifs
  · exact cp_jacobi _ _ _ _
  · simp

theorem cq_closed {lev : Fin n → ℕ} {S : Lt n → Prop} (h : IsSubL lev S) (i j k : Lt n) (hi : S i) (hj : S j)
    (hc : cq i j k ≠ 0) : S k := by
  obtain ⟨s, p⟩ := i
  obtain ⟨t, q⟩ := j
  obtain ⟨u, r⟩ := k
  have hu : u = (s == t) := by
    by_contra hne
    exact hc (if_neg hne)
  subst hu
  have hcp : cp p q r ≠ 0 := by
    intro h0
    exact hc (by simp [cq, h0])
  by_cases h1 : p.1.2 = q.1.1 ∧ r.1 = (p.1.1, q.1.2)
  · exact h.2 s t p q r h1.1 (by rw [h1.2]) (by rw [h1.2]) hi hj
  · by_cases h2 : q.1.2 = p.1.1 ∧ r.1 = (q.1.1, p.1.2)
    · have e : (t == s) = (s == t) := by cases s <;> cases t <;> rfl
      have := h.2 t s q p r h2.1 (by rw [h2.2]) (by rw [h2.2]) hj hi
      rwa [e] at this
    · exact absurd (by simp [cp, h1, h2]) hcp

theorem inUL_sub (lev : Fin n → ℕ) : IsSubL lev (inUL lev) := by
  refine ⟨fun _ h => h, fun s t i j k h1 h2 h3 hi hj => ?_⟩
  show lev k.1.1 < lev k.1.2
  have hi' : lev i.1.1 < lev i.1.2 := hi
  have hj' : lev j.1.1 < lev j.1.2 := hj
  rw [h2, h3]
  rw [h1] at hi'
  omega

end Constants

section Bd

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem Ts_comm {E1 E2 : Fin n → Fin n → Module.End ℂ V} (h : PairRel E1 E2) (s t : Bool) (a b c d : Fin n) :
    Ts E1 E2 s a b * Ts E1 E2 t c d - Ts E1 E2 t c d * Ts E1 E2 s a b =
      (if b = c then Ts E1 E2 (s == t) a d else 0) - (if d = a then Ts E1 E2 (s == t) c b else 0) := by
  have h1 := h.1 a b c d
  have h2 := h.2.1 a b c d
  have c1 : E1 a b * E2 c d = E2 c d * E1 a b := (h.2.2 a b c d).eq
  have c2 : E1 c d * E2 a b = E2 a b * E1 c d := (h.2.2 c d a b).eq
  have e1 : (E1 a b + E2 a b) * (E1 c d + E2 c d) - (E1 c d + E2 c d) * (E1 a b + E2 a b) =
      (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b) := by
    simp only [add_mul, mul_add, c1, c2]; abel
  have e2 : (E1 a b + E2 a b) * (E1 c d - E2 c d) - (E1 c d - E2 c d) * (E1 a b + E2 a b) =
      (E1 a b * E1 c d - E1 c d * E1 a b) - (E2 a b * E2 c d - E2 c d * E2 a b) := by
    simp only [add_mul, mul_add, sub_mul, mul_sub, c1, c2]; abel
  have e3 : (E1 a b - E2 a b) * (E1 c d + E2 c d) - (E1 c d + E2 c d) * (E1 a b - E2 a b) =
      (E1 a b * E1 c d - E1 c d * E1 a b) - (E2 a b * E2 c d - E2 c d * E2 a b) := by
    simp only [add_mul, mul_add, sub_mul, mul_sub, c1, c2]; abel
  have e4 : (E1 a b - E2 a b) * (E1 c d - E2 c d) - (E1 c d - E2 c d) * (E1 a b - E2 a b) =
      (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b) := by
    simp only [sub_mul, mul_sub, c1, c2]; abel
  have b1 : (false == true) = false := rfl
  have b2 : (true == false) = false := rfl
  have b3 : (false == false) = true := rfl
  have b4 : (true == true) = true := rfl
  cases s <;> cases t <;> simp only [Ts, Bool.false_eq_true, if_false, if_true, e1, e2, e3, e4, h1, h2, b1, b2, b3, b4] <;>
    split_ifs <;> first | abel | (simp; done) | (simp; abel)

theorem Tl_comm {E1 E2 : Fin n → Fin n → Module.End ℂ V} (h : PairRel E1 E2) (i j : Lt n) :
    Tl E1 E2 i * Tl E1 E2 j - Tl E1 E2 j * Tl E1 E2 i = ∑ k, cq i j k • Tl E1 E2 k := by
  obtain ⟨s, p⟩ := i
  obtain ⟨t, q⟩ := j
  have e : ∑ k, cq (s, p) (t, q) k • Tl E1 E2 k = ∑ r : Pos n, cp p q r • Tl E1 E2 (s == t, r) := by
    rw [Fintype.sum_prod_type]
    cases s <;> cases t <;> simp [cq]
  rw [e]
  exact (Ts_comm h s t _ _ _ _).trans (sum_cp (fun a b => Ts E1 E2 (s == t) a b) p q).symm

def tq (i j k : Lt n) : ℂ :=
  if k.1 = (i.1 == j.1) ∧ i.2.1.2 = j.2.1.1 ∧ k.2.1 = (i.2.1.1, j.2.1.2) then 1 else 0

theorem cq_eq (i j k : Lt n) : cq i j k = tq i j k - tq j i k := by
  have e : (j.1 == i.1) = (i.1 == j.1) := by cases i.1 <;> cases j.1 <;> rfl
  by_cases h : k.1 = (i.1 == j.1)
  · simp [cq, tq, cp, e, h]
  · simp [cq, tq, e, h]

theorem bracket_eq :
    (∑ s : Bool, ∑ t : Bool, ∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n,
      if i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2 then
        (creq ((s == t), k) * annq (t, j) * annq (s, i) : Module.End ℂ (Cq n V)) else 0) =
    (1 / 2 : ℂ) • ∑ i : Lt n, ∑ j : Lt n, ∑ k : Lt n, cq i j k • (creq k * annq j * annq i : Module.End ℂ (Cq n V)) := by
  set X : Lt n → Lt n → Lt n → Module.End ℂ (Cq n V) := fun i j k => creq k * annq j * annq i with hX
  have hanti : ∀ i j k, X j i k = - X i j k := by
    intro i j k
    have := ann_ann (V := V) i j
    simp only [hX]
    rw [mul_assoc, mul_assoc, ← mul_neg, eq_neg_of_add_eq_zero_left this]
  have hU : (∑ s : Bool, ∑ t : Bool, ∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n,
      if i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2 then
        (creq ((s == t), k) * annq (t, j) * annq (s, i) : Module.End ℂ (Cq n V)) else 0) =
      ∑ i : Lt n, ∑ j : Lt n, ∑ k : Lt n, tq i j k • X i j k := by
    simp only [Fintype.sum_prod_type (f := fun i : Lt n => _)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single (s == i) (fun u _ hu => Finset.sum_eq_zero fun y _ => by simp [tq, hu]) (by simp)]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : t.1.2 = j.1.1 ∧ k.1.1 = t.1.1 ∧ k.1.2 = j.1.2
    · rw [if_pos h, tq, if_pos ⟨rfl, h.1, Prod.ext h.2.1 h.2.2⟩, one_smul]
    · refine (if_neg h).trans ?_
      rw [tq, if_neg, zero_smul]
      intro h'
      have h2 : k.1 = (t.1.1, j.1.2) := h'.2.2
      exact h ⟨h'.2.1, by rw [h2], by rw [h2]⟩
  have hV : ∑ i : Lt n, ∑ j : Lt n, ∑ k : Lt n, tq j i k • X i j k = - ∑ i : Lt n, ∑ j : Lt n, ∑ k : Lt n, tq i j k • X i j k := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hanti, smul_neg]
  show _ = (1 / 2 : ℂ) • ∑ i : Lt n, ∑ j : Lt n, ∑ k : Lt n, cq i j k • X i j k
  rw [hU]
  simp only [cq_eq, sub_smul, Finset.sum_sub_distrib]
  rw [hV, sub_neg_eq_add, ← two_smul ℂ, smul_smul]
  norm_num

theorem bdq_eq (E1 E2 : Fin n → Fin n → Module.End ℂ V) :
    bdq E1 E2 = (∑ i : Lt n, (liftq n (Tl E1 E2 i) : Module.End ℂ (Cq n V)) * annq i) +
      (1 / 2 : ℂ) • ∑ i : Lt n, ∑ j : Lt n, ∑ k : Lt n, cq i j k • (creq k * annq j * annq i) := by
  rw [bdq, bracket_eq]

theorem bdq_sq {E1 E2 : Fin n → Fin n → Module.End ℂ V} (h : PairRel E1 E2) : bdq E1 E2 * bdq E1 E2 = 0 := by
  have hL : ∀ i j : Lt n, (liftq n (Tl E1 E2 i) : Module.End ℂ (Cq n V)) * liftq n (Tl E1 E2 j) -
      liftq n (Tl E1 E2 j) * liftq n (Tl E1 E2 i) = ∑ k, cq i j k • (liftq n (Tl E1 E2 k) : Module.End ℂ (Cq n V)) := by
    intro i j
    refine LinearMap.ext fun x => funext fun A => ?_
    have := LinearMap.congr_fun (Tl_comm h i j) (x A)
    simpa [lift_apply, LinearMap.sum_apply, Finset.sum_apply] using this
  rw [bdq_eq]
  exact d_sq cq (fun i => (liftq n (Tl E1 E2 i) : Module.End ℂ (Cq n V))) annq creq hL
    (fun i j => lift_ann _ j) (fun i j => lift_cre _ j) cq_anti cq_jacobi ann_ann cre_cre ann_cre

end Bd

section Supp

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem lift_ann' (T : V →ₗ[ℂ] W) (i : Lt n) (x : Cq n V) :
    liftq n T (annq i x) = annq i (liftq n T x) := by
  funext A
  by_cases h : i ∈ A <;> simp [ann_apply, lift_apply, h]

theorem lift_cre' (T : V →ₗ[ℂ] W) (i : Lt n) (x : Cq n V) :
    liftq n T (creq i x) = creq i (liftq n T x) := by
  funext A
  by_cases h : i ∈ A <;> simp [cre_apply, lift_apply, h]

theorem bd_apply (E1 E2 : Fin n → Fin n → Module.End ℂ V) (x : Cq n V) :
    bdq E1 E2 x = ∑ i : Lt n, liftq n (Tl E1 E2 i) (annq i x) +
      (1 / 2 : ℂ) • ∑ i : Lt n, ∑ j : Lt n, ∑ k : Lt n, cq i j k • creq k (annq j (annq i x)) := by
  rw [bdq_eq]
  simp [Module.End.mul_apply, LinearMap.sum_apply]

def supSub (V : Type) [AddCommGroup V] [Module ℂ V] (P : Finset (Lt n) → Prop) : Submodule ℂ (Cq n V) where
  carrier := {x | ∀ A, x A ≠ 0 → P A}
  add_mem' := by
    intro x y hx hy A h
    by_contra hP
    have h1 := not_not.mp (mt (hx A) hP)
    have h2 := not_not.mp (mt (hy A) hP)
    exact h (by simp [h1, h2])
  zero_mem' := fun A h => absurd rfl h
  smul_mem' := by
    intro c x hx A h
    by_contra hP
    have h1 := not_not.mp (mt (hx A) hP)
    exact h (by simp [h1])

theorem lift_mem {P : Finset (Lt n) → Prop} (T : V →ₗ[ℂ] W) {x : Cq n V} (hx : x ∈ supSub V P) :
    liftq n T x ∈ supSub W P := by
  intro A hA
  refine hx A fun h => hA ?_
  simp [lift_apply, h]

theorem ann_ne {i : Lt n} {x : Cq n V} {A : Finset (Lt n)} (h : annq i x A ≠ 0) :
    i ∉ A ∧ x (insert i A) ≠ 0 := by
  by_cases hi : i ∈ A
  · exact absurd (by rw [ann_apply, if_pos hi]) h
  · refine ⟨hi, fun h0 => h ?_⟩
    rw [ann_apply, if_neg hi, h0, smul_zero]

theorem cre_ne {i : Lt n} {x : Cq n V} {A : Finset (Lt n)} (h : creq i x A ≠ 0) :
    i ∈ A ∧ x (A.erase i) ≠ 0 := by
  by_cases hi : i ∈ A
  · refine ⟨hi, fun h0 => h ?_⟩
    rw [cre_apply, if_pos hi, h0, smul_zero]
  · exact absurd (by rw [cre_apply, if_neg hi]) h

theorem ann_deg {m : ℕ} (i : Lt n) {x : Cq n V} (hx : DegQ (m + 1) x) : DegQ m (annq i x) := by
  intro A hA
  obtain ⟨h1, h2⟩ := ann_ne hA
  have := hx _ h2
  rw [card_insert_of_notMem h1] at this
  omega

theorem ann_eq_zero_of_degree_zero (i : Lt n) {x : Cq n V} (hx : DegQ 0 x) : annq i x = 0 := by
  funext A
  by_contra hA
  obtain ⟨h1, h2⟩ := ann_ne hA
  have := hx _ h2
  rw [card_insert_of_notMem h1] at this
  omega

theorem cre_deg {m : ℕ} (i : Lt n) {x : Cq n V} (hx : DegQ m x) : DegQ (m + 1) (creq i x) := by
  intro A hA
  obtain ⟨h1, h2⟩ := cre_ne hA
  have := hx _ h2
  rw [card_erase_of_mem h1] at this
  have := card_pos.mpr ⟨i, h1⟩
  omega

theorem deg_iff {m : ℕ} {x : Cq n V} : DegQ m x ↔ x ∈ supSub V (fun A => A.card = m) := Iff.rfl

theorem supp_iff {S : Lt n → Prop} {x : Cq n V} : SuppQ S x ↔ x ∈ supSub V (fun A => ∀ i ∈ A, S i) := Iff.rfl

theorem bd_deg (E1 E2 : Fin n → Fin n → Module.End ℂ V) {m : ℕ} {x : Cq n V} (hx : DegQ (m + 1) x) :
    DegQ m (bdq E1 E2 x) := by
  rw [bd_apply, deg_iff]
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => lift_mem _ (ann_deg i hx)) ?_
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_)
  cases m with
  | zero =>
    rw [ann_eq_zero_of_degree_zero j (ann_deg i hx), map_zero]
    exact Submodule.zero_mem _
  | succ m => exact cre_deg k (ann_deg j (ann_deg i hx))

theorem ann_supp {S : Lt n → Prop} (i : Lt n) {x : Cq n V} (hx : SuppQ S x) : SuppQ S (annq i x) := by
  intro A hA l hl
  obtain ⟨_, h2⟩ := ann_ne hA
  exact hx _ h2 l (mem_insert_of_mem hl)

theorem ann_zero {S : Lt n → Prop} {i : Lt n} {x : Cq n V} (hx : SuppQ S x) (hi : ¬ S i) : annq i x = 0 := by
  funext A
  by_contra hA
  obtain ⟨_, h2⟩ := ann_ne hA
  exact hi (hx _ h2 i (mem_insert_self _ _))

theorem cre_supp {S : Lt n → Prop} {k : Lt n} (hk : S k) {x : Cq n V} (hx : SuppQ S x) : SuppQ S (creq k x) := by
  intro A hA l hl
  obtain ⟨_, h2⟩ := cre_ne hA
  by_cases hlk : l = k
  · exact hlk ▸ hk
  · exact hx _ h2 l (mem_erase.mpr ⟨hlk, hl⟩)

theorem bd_supp (E1 E2 : Fin n → Fin n → Module.End ℂ V) {S : Lt n → Prop}
    (hS : ∀ i j k, S i → S j → cq i j k ≠ 0 → S k) {x : Cq n V} (hx : SuppQ S x) :
    SuppQ S (bdq E1 E2 x) := by
  rw [bd_apply, supp_iff]
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => lift_mem _ (ann_supp i hx)) ?_
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
    Submodule.sum_mem _ fun k _ => ?_)
  by_cases hc : cq i j k = 0
  · rw [hc, zero_smul]
    exact Submodule.zero_mem _
  by_cases hi : S i
  · by_cases hj : S j
    · exact Submodule.smul_mem _ _ (cre_supp (hS i j k hi hj hc) (ann_supp j (ann_supp i hx)))
    · rw [ann_zero (ann_supp i hx) hj, map_zero, smul_zero]
      exact Submodule.zero_mem _
  · rw [ann_zero hx hi, map_zero, map_zero, smul_zero]
    exact Submodule.zero_mem _

end Supp

end GlobalTheory.CompanionTheory.PairMult.COU
