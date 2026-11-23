import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.InjectiveDecompositionAction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SgMulSelf

open Finset

noncomputable section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

namespace GlobalTheory.CompanionTheory.KPChains

open GlobalTheory.CompanionTheory.RealMult (cp Pair2)
open GlobalTheory.CompanionTheory.RealMult.BdSqProof (d_sq cp_jacobi sum_cp)
open CompanionTheory.D.LK (Pos)

variable {n : ℕ}

def cstL (i j k : Lt n) : ℂ := if k.1 = xor i.1 j.1 then cp i.2 j.2 k.2 else 0

def ttL (i j k : Lt n) : ℂ :=
  if i.2.1.2 = j.2.1.1 ∧ k.1 = xor i.1 j.1 ∧ k.2.1.1 = i.2.1.1 ∧ k.2.1.2 = j.2.1.2 then 1 else 0

def IsClosedL (S : Lt n → Prop) : Prop :=
  ∀ l m k : Lt n, S l → S m → l.2.1.2 = m.2.1.1 → k.1 = xor l.1 m.1 → k.2.1 = (l.2.1.1, m.2.1.2) → S k

theorem isClosedL_univ : IsClosedL (fun _ : Lt n => True) := fun _ _ _ _ _ _ _ _ => trivial

theorem isClosedL_isK : IsClosedL (isK (n := n)) := by
  intro l m k hl hm _ hk _
  simp only [isK] at hl hm ⊢
  simp [hk, hl, hm]

theorem cstL_eq (i j k : Lt n) : cstL i j k = ttL i j k - ttL j i k := by
  have e : ∀ p q : Lt n, (p.2.1.2 = q.2.1.1 ∧ k.1 = xor p.1 q.1 ∧ k.2.1.1 = p.2.1.1 ∧ k.2.1.2 = q.2.1.2) ↔
      (k.1 = xor p.1 q.1 ∧ p.2.1.2 = q.2.1.1 ∧ k.2.1 = (p.2.1.1, q.2.1.2)) := by
    intro p q
    rw [Prod.ext_iff]
    tauto
  simp only [cstL, ttL, cp, e, Bool.xor_comm j.1 i.1]
  by_cases h : k.1 = xor i.1 j.1 <;> simp [h, Prod.ext_iff]

theorem cstL_anti (i j k : Lt n) : cstL i j k = -cstL j i k := by
  rw [cstL_eq, cstL_eq]; ring

theorem sum_cstL (p q r k : Lt n) : ∑ i, cstL p q i * cstL i r k =
    if k.1 = xor (xor p.1 q.1) r.1 then ∑ m, cp p.2 q.2 m * cp m r.2 k.2 else 0 := by
  obtain ⟨s, p⟩ := p
  obtain ⟨t, q⟩ := q
  obtain ⟨u, r⟩ := r
  obtain ⟨w, k⟩ := k
  rw [Fintype.sum_prod_type]
  cases s <;> cases t <;> cases u <;> cases w <;> simp [cstL]

theorem cstL_jacobi (p q r k : Lt n) :
    ∑ i, cstL p q i * cstL i r k + ∑ i, cstL q r i * cstL i p k + ∑ i, cstL r p i * cstL i q k = 0 := by
  rw [sum_cstL, sum_cstL, sum_cstL]
  have h1 : xor (xor q.1 r.1) p.1 = xor (xor p.1 q.1) r.1 := by cases p.1 <;> cases q.1 <;> cases r.1 <;> rfl
  have h2 : xor (xor r.1 p.1) q.1 = xor (xor p.1 q.1) r.1 := by cases p.1 <;> cases q.1 <;> cases r.1 <;> rfl
  rw [h1, h2]
  split_ifs
  · exact cp_jacobi _ _ _ _
  · simp

theorem cstL_supp {S : Lt n → Prop} (hS : IsClosedL S) {i j k : Lt n} (hi : S i) (hj : S j) (hk : ¬S k) :
    cstL i j k = 0 := by
  simp only [cstL]
  split_ifs with hw
  swap
  · rfl
  have a1 : ¬(i.2.1.2 = j.2.1.1 ∧ k.2.1 = (i.2.1.1, j.2.1.2)) := fun h => hk (hS i j k hi hj h.1 hw h.2)
  have a2 : ¬(j.2.1.2 = i.2.1.1 ∧ k.2.1 = (j.2.1.1, i.2.1.2)) := fun h =>
    hk (hS j i k hj hi h.1 (hw.trans (Bool.xor_comm _ _)) h.2)
  simp [cp, a1, a2]

open Classical in

theorem sum_sub (S : Lt n → Prop) {M : Type*} [AddCommMonoid M] (f : Lt n → M) :
    ∑ k : {l // S l}, f k.1 = ∑ k, if S k then f k else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) f).symm

theorem half_sum {ι M : Type*} [Fintype ι] [AddCommGroup M] [Module ℂ M] (t : ι → ι → ι → ℂ) (Y : ι → ι → ι → M)
    (hY : ∀ i j k, Y j i k = -Y i j k) :
    (1 / 2 : ℂ) • ∑ i, ∑ j, ∑ k, (t i j k - t j i k) • Y i j k = ∑ i, ∑ j, ∑ k, t i j k • Y i j k := by
  have e : ∑ i, ∑ j, ∑ k, t j i k • Y i j k = -∑ i, ∑ j, ∑ k, t i j k • Y i j k := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hY i j k, smul_neg]
  simp only [sub_smul, Finset.sum_sub_distrib]
  rw [e, sub_neg_eq_add, ← two_smul ℂ, smul_smul]
  norm_num

section Ring

variable {R : Type} [Ring R] [Algebra ℂ R]

open Classical in

def partA (S : Lt n → Prop) (X an : Lt n → R) : R := ∑ l, if S l then X l * an l else 0

open Classical in

def partB (S : Lt n → Prop) (an cr : Lt n → R) : R :=
  ∑ l : Lt n, ∑ m : Lt n, ∑ k : Lt n,
    if S l ∧ S m ∧ l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧ k.2.1.1 = l.2.1.1 ∧ k.2.1.2 = m.2.1.2 then
      cr k * an m * an l else 0

open Classical in

theorem partB_eq {S : Lt n → Prop} (hS : IsClosedL S) (an cr : Lt n → R) (haa : ∀ i j, an i * an j + an j * an i = 0) :
    (1 / 2 : ℂ) • ∑ i : {l // S l}, ∑ j : {l // S l}, ∑ k : {l // S l},
      cstL i.1 j.1 k.1 • (cr k.1 * an j.1 * an i.1) = partB S an cr := by
  have hY : ∀ (i j k : {l // S l}), cr k.1 * an i.1 * an j.1 = -(cr k.1 * an j.1 * an i.1) := by
    intro i j k
    rw [mul_assoc, eq_neg_of_add_eq_zero_left (haa i.1 j.1), mul_neg, mul_assoc]
  simp only [cstL_eq]
  rw [half_sum (fun i j k : {l // S l} => ttL i.1 j.1 k.1) (fun i j k : {l // S l} => cr k.1 * an j.1 * an i.1) hY]
  have e1 : ∀ i j : {l // S l}, ∑ k : {l // S l}, ttL i.1 j.1 k.1 • (cr k.1 * an j.1 * an i.1) =
      ∑ k : Lt n, if S i.1 ∧ S j.1 ∧ i.1.2.1.2 = j.1.2.1.1 ∧ k.1 = xor i.1.1 j.1.1 ∧ k.2.1.1 = i.1.2.1.1 ∧
        k.2.1.2 = j.1.2.1.2 then cr k * an j.1 * an i.1 else 0 := by
    intro i j
    rw [sum_sub S (fun k => ttL i.1 j.1 k • (cr k * an j.1 * an i.1))]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hc : i.1.2.1.2 = j.1.2.1.1 ∧ k.1 = xor i.1.1 j.1.1 ∧ k.2.1.1 = i.1.2.1.1 ∧ k.2.1.2 = j.1.2.1.2
    · have hk : S k := hS i.1 j.1 k i.2 j.2 hc.1 hc.2.1 (Prod.ext hc.2.2.1 hc.2.2.2)
      simp [ttL, hc, hk, i.2, j.2]
    · have hc' : ¬(S i.1 ∧ S j.1 ∧ i.1.2.1.2 = j.1.2.1.1 ∧ k.1 = xor i.1.1 j.1.1 ∧ k.2.1.1 = i.1.2.1.1 ∧
          k.2.1.2 = j.1.2.1.2) := fun h => hc h.2.2
      rw [if_neg hc']
      simp [ttL, hc]
  simp only [e1]
  have e2 : ∀ G : Lt n → Lt n → R, (∀ i j, ¬(S i ∧ S j) → G i j = 0) →
      ∑ i : {l // S l}, ∑ j : {l // S l}, G i.1 j.1 = ∑ i, ∑ j, G i j := by
    intro G hG
    rw [sum_sub S (fun i => ∑ j : {l // S l}, G i j.1)]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : S i
    · rw [if_pos hi, sum_sub S (G i)]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs with hj
      · rfl
      · exact (hG i j fun h => hj h.2).symm
    · rw [if_neg hi]
      exact (Finset.sum_eq_zero fun j _ => hG i j fun h => hi h.1).symm
  rw [e2 (fun i j => ∑ k : Lt n, if S i ∧ S j ∧ i.2.1.2 = j.2.1.1 ∧ k.1 = xor i.1 j.1 ∧ k.2.1.1 = i.2.1.1 ∧
        k.2.1.2 = j.2.1.2 then cr k * an j * an i else 0)]
  · rfl
  · intro i j hij
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg fun h => hij ⟨h.1, h.2.1⟩]

open Classical in

theorem part_sq {S : Lt n → Prop} (hS : IsClosedL S) (X an cr : Lt n → R)
    (hX : ∀ i j, S i → S j → X i * X j - X j * X i = ∑ k, cstL i j k • X k)
    (h1 : ∀ i j, Commute (X i) (an j)) (h2 : ∀ i j, Commute (X i) (cr j))
    (haa : ∀ i j, an i * an j + an j * an i = 0) (hcc : ∀ i j, cr i * cr j + cr j * cr i = 0)
    (hac : ∀ i j, an i * cr j + cr j * an i = if i = j then 1 else 0) :
    (partA S X an + partB S an cr) * (partA S X an + partB S an cr) = 0 := by
  have eA : ∑ i : {l // S l}, X i.1 * an i.1 = partA S X an := sum_sub S fun l => X l * an l
  have hL : ∀ i j : {l // S l}, X i.1 * X j.1 - X j.1 * X i.1 = ∑ k : {l // S l}, cstL i.1 j.1 k.1 • X k.1 := by
    intro i j
    rw [hX i.1 j.1 i.2 j.2, sum_sub S fun k => cstL i.1 j.1 k • X k]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · rfl
    · rw [cstL_supp hS i.2 j.2 hk, zero_smul]
  have hJ : ∀ p q r k : {l // S l}, ∑ i : {l // S l}, cstL p.1 q.1 i.1 * cstL i.1 r.1 k.1 +
      ∑ i : {l // S l}, cstL q.1 r.1 i.1 * cstL i.1 p.1 k.1 +
      ∑ i : {l // S l}, cstL r.1 p.1 i.1 * cstL i.1 q.1 k.1 = 0 := by
    intro p q r k
    have e : ∀ a b c : {l // S l}, ∑ i : {l // S l}, cstL a.1 b.1 i.1 * cstL i.1 c.1 k.1 =
        ∑ i, cstL a.1 b.1 i * cstL i c.1 k.1 := by
      intro a b c
      rw [sum_sub S fun i => cstL a.1 b.1 i * cstL i c.1 k.1]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with hi
      · rfl
      · rw [cstL_supp hS a.2 b.2 hi, zero_mul]
    rw [e, e, e]
    exact cstL_jacobi _ _ _ _
  have hd := d_sq (ι := {l // S l}) (fun i j k => cstL i.1 j.1 k.1) (fun i => X i.1) (fun i => an i.1) (fun i => cr i.1)
    hL (fun i j => h1 _ _) (fun i j => h2 _ _) (fun i j k => cstL_anti _ _ _) hJ (fun i j => haa _ _)
    (fun i j => hcc _ _) (fun i j => by
      have := hac i.1 j.1
      simpa only [Subtype.ext_iff] using this)
  rw [eA, partB_eq hS an cr haa] at hd
  exact hd

end Ring

section Chains

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem xL_comm {E1 E2 : Fin n → Fin n → Module.End ℂ V} (h : Pair2 E1 E2) (i j : Lt n) :
    xL E1 E2 i * xL E1 E2 j - xL E1 E2 j * xL E1 E2 i = ∑ k, cstL i j k • xL E1 E2 k := by
  obtain ⟨s, p⟩ := i
  obtain ⟨t, q⟩ := j
  have e : ∑ k, cstL (s, p) (t, q) k • xL E1 E2 k = ∑ r : Pos n, cp p q r • xL E1 E2 (xor s t, r) := by
    rw [Fintype.sum_prod_type]
    cases s <;> cases t <;> simp [cstL]
  rw [e]
  have g1 := h.gl1 p.1.1 p.1.2 q.1.1 q.1.2
  have g2 := h.gl2 p.1.1 p.1.2 q.1.1 q.1.2
  have c1 := h.comm p.1.1 p.1.2 q.1.1 q.1.2
  have c2 := h.comm q.1.1 q.1.2 p.1.1 p.1.2
  have sK : ∑ r : Pos n, cp p q r • xL E1 E2 (false, r) = _ := sum_cp (fun a b => E1 a b + E2 a b) p q
  have sP : ∑ r : Pos n, cp p q r • xL E1 E2 (true, r) = _ := sum_cp (fun a b => E1 a b - E2 a b) p q
  cases s <;> cases t
  · change (E1 p.1.1 p.1.2 + E2 p.1.1 p.1.2) * (E1 q.1.1 q.1.2 + E2 q.1.1 q.1.2) -
      (E1 q.1.1 q.1.2 + E2 q.1.1 q.1.2) * (E1 p.1.1 p.1.2 + E2 p.1.1 p.1.2) = ∑ r : Pos n, cp p q r • xL E1 E2 (false, r)
    have e : (E1 p.1.1 p.1.2 + E2 p.1.1 p.1.2) * (E1 q.1.1 q.1.2 + E2 q.1.1 q.1.2) -
        (E1 q.1.1 q.1.2 + E2 q.1.1 q.1.2) * (E1 p.1.1 p.1.2 + E2 p.1.1 p.1.2) =
        (E1 p.1.1 p.1.2 * E1 q.1.1 q.1.2 - E1 q.1.1 q.1.2 * E1 p.1.1 p.1.2) +
          (E2 p.1.1 p.1.2 * E2 q.1.1 q.1.2 - E2 q.1.1 q.1.2 * E2 p.1.1 p.1.2) := by
      simp only [add_mul, mul_add, c1, ← c2]
      abel
    rw [sK, e, g1, g2]
    split_ifs <;> abel
  · change (E1 p.1.1 p.1.2 + E2 p.1.1 p.1.2) * (E1 q.1.1 q.1.2 - E2 q.1.1 q.1.2) -
      (E1 q.1.1 q.1.2 - E2 q.1.1 q.1.2) * (E1 p.1.1 p.1.2 + E2 p.1.1 p.1.2) = ∑ r : Pos n, cp p q r • xL E1 E2 (true, r)
    have e : (E1 p.1.1 p.1.2 + E2 p.1.1 p.1.2) * (E1 q.1.1 q.1.2 - E2 q.1.1 q.1.2) -
        (E1 q.1.1 q.1.2 - E2 q.1.1 q.1.2) * (E1 p.1.1 p.1.2 + E2 p.1.1 p.1.2) =
        (E1 p.1.1 p.1.2 * E1 q.1.1 q.1.2 - E1 q.1.1 q.1.2 * E1 p.1.1 p.1.2) -
          (E2 p.1.1 p.1.2 * E2 q.1.1 q.1.2 - E2 q.1.1 q.1.2 * E2 p.1.1 p.1.2) := by
      simp only [add_mul, mul_add, sub_mul, mul_sub, c1, ← c2]
      abel
    rw [sP, e, g1, g2]
    split_ifs <;> abel
  · change (E1 p.1.1 p.1.2 - E2 p.1.1 p.1.2) * (E1 q.1.1 q.1.2 + E2 q.1.1 q.1.2) -
      (E1 q.1.1 q.1.2 + E2 q.1.1 q.1.2) * (E1 p.1.1 p.1.2 - E2 p.1.1 p.1.2) = ∑ r : Pos n, cp p q r • xL E1 E2 (true, r)
    have e : (E1 p.1.1 p.1.2 - E2 p.1.1 p.1.2) * (E1 q.1.1 q.1.2 + E2 q.1.1 q.1.2) -
        (E1 q.1.1 q.1.2 + E2 q.1.1 q.1.2) * (E1 p.1.1 p.1.2 - E2 p.1.1 p.1.2) =
        (E1 p.1.1 p.1.2 * E1 q.1.1 q.1.2 - E1 q.1.1 q.1.2 * E1 p.1.1 p.1.2) -
          (E2 p.1.1 p.1.2 * E2 q.1.1 q.1.2 - E2 q.1.1 q.1.2 * E2 p.1.1 p.1.2) := by
      simp only [add_mul, mul_add, sub_mul, mul_sub, c1, ← c2]
      abel
    rw [sP, e, g1, g2]
    split_ifs <;> abel
  · change (E1 p.1.1 p.1.2 - E2 p.1.1 p.1.2) * (E1 q.1.1 q.1.2 - E2 q.1.1 q.1.2) -
      (E1 q.1.1 q.1.2 - E2 q.1.1 q.1.2) * (E1 p.1.1 p.1.2 - E2 p.1.1 p.1.2) = ∑ r : Pos n, cp p q r • xL E1 E2 (false, r)
    have e : (E1 p.1.1 p.1.2 - E2 p.1.1 p.1.2) * (E1 q.1.1 q.1.2 - E2 q.1.1 q.1.2) -
        (E1 q.1.1 q.1.2 - E2 q.1.1 q.1.2) * (E1 p.1.1 p.1.2 - E2 p.1.1 p.1.2) =
        (E1 p.1.1 p.1.2 * E1 q.1.1 q.1.2 - E1 q.1.1 q.1.2 * E1 p.1.1 p.1.2) +
          (E2 p.1.1 p.1.2 * E2 q.1.1 q.1.2 - E2 q.1.1 q.1.2 * E2 p.1.1 p.1.2) := by
      simp only [sub_mul, mul_sub, c1, ← c2]
      abel
    rw [sK, e, g1, g2]
    split_ifs <;> abel

end Chains

theorem bdSqL : PositivityTheory.RgBcC.RealD.BdSqL := by
  intro n S hS V _ _ E1 E2 hE
  have h : Pair2 E1 E2 := ⟨hE.1, hE.2.1, hE.2.2⟩
  have hX : ∀ i j : Lt n, (liftL n (xL E1 E2 i) : Module.End ℂ (Cq n V)) * liftL n (xL E1 E2 j) -
      liftL n (xL E1 E2 j) * liftL n (xL E1 E2 i) = ∑ k, cstL i j k • (liftL n (xL E1 E2 k) : Module.End ℂ (Cq n V)) := by
    intro i j
    refine LinearMap.ext fun x => funext fun A => ?_
    have := LinearMap.congr_fun (xL_comm h i j) (x A)
    simpa [liftL, LinearMap.sum_apply, Finset.sum_apply] using this
  exact part_sq hS (fun i => (liftL n (xL E1 E2 i) : Module.End ℂ (Cq n V))) annL creL (fun i j _ _ => hX i j)
    (fun i j => GlobalTheory.CompanionTheory.RealMult.BdSqProof.lift_ann _ j) (fun i j => GlobalTheory.CompanionTheory.RealMult.BdSqProof.lift_cre _ j)
    GlobalTheory.CompanionTheory.RealMult.BdSqProof.ann_ann GlobalTheory.CompanionTheory.RealMult.BdSqProof.cre_cre GlobalTheory.CompanionTheory.RealMult.BdSqProof.ann_cre

end GlobalTheory.CompanionTheory.KPChains
