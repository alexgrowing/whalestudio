import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.OrderedCreationCommutesPastLevi

open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

noncomputable section

namespace GlobalTheory.CompanionTheory.RgCOBlock.LeviBd

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem units_mul_relation_rearrange_commRing {R : Type*} [Ring R] (a b c d : R) (h1 : b * c + c * b = d) (h2 : a * b + b * a = 0) :
    c * a * b - b * (c * a) = -(d * a) := by
  subst h1
  have h3 : a * b = -(b * a) := eq_neg_of_add_eq_zero_left h2
  rw [mul_assoc, h3]
  noncomm_ring

theorem term_ann (k i l : Pos n) :
    (cre k * ann i * ann l - ann l * (cre k * ann i) : Module.End ℂ (Cn n V)) =
      -(if l = k then ann i else 0) := by
  rw [units_mul_relation_rearrange_commRing (ann i) (ann l) (cre k) _ (CompanionTheory.D.LK.Car.ann_cre l k) (CompanionTheory.D.LK.Car.ann_ann i l)]
  split_ifs <;> simp

theorem adL_ann (p q : Fin n) (l : Pos n) :
    (adL p q * ann l - ann l * adL p q : Module.End ℂ (Cn n V)) = -∑ i : Pos n, adC p q i l • ann i := by
  have h : (adL p q * ann l - ann l * adL p q : Module.End ℂ (Cn n V)) =
      ∑ i : Pos n, ∑ k : Pos n, adC p q i k • (cre k * ann i * ann l - ann l * (cre k * ann i)) := by
    simp only [adL, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_sub,
      ← Finset.sum_sub_distrib]
  rw [h]
  simp only [term_ann, smul_neg, Finset.sum_neg_distrib, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]

theorem lift_mul_ann (T : Module.End ℂ V) (i : Pos n) :
    ((lift n T : Module.End ℂ (Cn n V)) * ann i : Module.End ℂ (Cn n V)) = ann i * (lift n T : Module.End ℂ (Cn n V)) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [Module.End.mul_apply, CompanionTheory.D.LK.lift_apply, CompanionTheory.D.LK.Car.ann_apply]
  split_ifs <;> simp

theorem lift_mul_cre (T : Module.End ℂ V) (i : Pos n) :
    ((lift n T : Module.End ℂ (Cn n V)) * cre i : Module.End ℂ (Cn n V)) = cre i * (lift n T : Module.End ℂ (Cn n V)) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [Module.End.mul_apply, CompanionTheory.D.LK.lift_apply, CompanionTheory.D.LK.Car.cre_apply]
  split_ifs <;> simp

theorem adL_mul_lift (T : Module.End ℂ V) (p q : Fin n) :
    (adL p q * (lift n T : Module.End ℂ (Cn n V)) : Module.End ℂ (Cn n V)) = (lift n T : Module.End ℂ (Cn n V)) * adL p q := by
  simp only [adL, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_assoc, ← lift_mul_ann, ← mul_assoc, ← lift_mul_cre, mul_assoc]

theorem lift_mul (S T : Module.End ℂ V) :
    (lift n (S * T) : Module.End ℂ (Cn n V)) = (lift n S : Module.End ℂ (Cn n V)) * (lift n T : Module.End ℂ (Cn n V)) := rfl

theorem lift_sub (S T : Module.End ℂ V) :
    (lift n (S - T) : Module.End ℂ (Cn n V)) = (lift n S : Module.End ℂ (Cn n V)) - (lift n T : Module.End ℂ (Cn n V)) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp

theorem lift_sum {ι : Type*} (s : Finset ι) (f : ι → Module.End ℂ V) :
    (lift n (∑ i ∈ s, f i) : Module.End ℂ (Cn n V)) = ∑ i ∈ s, (lift n (f i) : Module.End ℂ (Cn n V)) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp [LinearMap.sum_apply, Finset.sum_apply]

theorem lift_smul (c : ℂ) (S : Module.End ℂ V) :
    (lift n (c • S) : Module.End ℂ (Cn n V)) = c • (lift n S : Module.End ℂ (Cn n V)) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp

theorem lF_ann (E : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) (l : Pos n) :
    (lF E p q * ann l - ann l * lF E p q : Module.End ℂ (Cn n V)) = -∑ i : Pos n, adC p q i l • ann i := by
  rw [← adL_ann, lF, add_mul, mul_add, lift_mul_ann]
  abel

theorem lF_cre' (E : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) (l : Pos n) :
    (lF E p q * cre l - cre l * lF E p q : Module.End ℂ (Cn n V)) = ∑ k : Pos n, adC p q l k • cre k := by
  rw [GlobalTheory.CompanionTheory.FarReg.BdProd.lF_cre]
  abel

theorem lF_lift (E : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) (T : Module.End ℂ V) :
    (lF E p q * (lift n T : Module.End ℂ (Cn n V)) - (lift n T : Module.End ℂ (Cn n V)) * lF E p q : Module.End ℂ (Cn n V)) =
      lift n (E p q * T - T * E p q) := by
  rw [lF, add_mul, mul_add, adL_mul_lift, lift_sub, lift_mul, lift_mul]
  abel

def tc (i j k : Pos n) : ℂ := if i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2 then 1 else 0

def S1 (E : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ (Cn n V) :=
  ∑ i : Pos n, (lift n (E i.1.1 i.1.2) : Module.End ℂ (Cn n V)) * ann i

def Wt3 (V : Type) [AddCommGroup V] [Module ℂ V] (a b m : Pos n) : Module.End ℂ (Cn n V) := cre m * ann b * ann a

def S2 (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] : Module.End ℂ (Cn n V) :=
  ∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n, tc i j k • Wt3 V i j k

theorem bd_eq (E : Fin n → Fin n → Module.End ℂ V) : bd (allT n) E = S1 E + S2 n V := by
  unfold bd S1 S2 tc Wt3
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases h : i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2
  · rw [if_pos ⟨rfl, rfl, h⟩, if_pos h, one_smul]
  · rw [if_neg (fun c => h c.2.2), if_neg h, zero_smul]

theorem comm3 {R : Type*} [Ring R] (L c a b dc da db : R) (hc : L * c - c * L = dc) (ha : L * a - a * L = da)
    (hb : L * b - b * L = db) : L * (c * a * b) - c * a * b * L = dc * a * b + c * da * b + c * a * db := by
  subst hc ha hb
  noncomm_ring

theorem term2 (E : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) (i j k : Pos n) :
    (lF E p q * Wt3 V i j k - Wt3 V i j k * lF E p q : Module.End ℂ (Cn n V)) =
      ∑ m : Pos n, adC p q k m • Wt3 V i j m - ∑ l : Pos n, adC p q l j • Wt3 V i l k -
        ∑ l : Pos n, adC p q l i • Wt3 V l j k := by
  unfold Wt3
  rw [comm3 _ _ _ _ _ _ _ (lF_cre' E p q k) (lF_ann E p q j) (lF_ann E p q i)]
  simp only [Finset.sum_mul, Finset.mul_sum, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm]
  abel

def Dc (p q : Fin n) (a b m : Pos n) : ℂ :=
  ∑ k : Pos n, tc a b k * adC p q k m - ∑ j : Pos n, tc a j m * adC p q b j - ∑ i : Pos n, tc i b m * adC p q a i

theorem reindex {M : Type*} [AddCommGroup M] [Module ℂ M] (c : Pos n → Pos n → Pos n → ℂ) (d : Pos n → Pos n → ℂ)
    (w : Pos n → Pos n → Pos n → M) :
    ∑ i, ∑ j, ∑ k, c i j k • (∑ m, d k m • w i j m - ∑ l, d l j • w i l k - ∑ l, d l i • w l j k) =
      ∑ a, ∑ b, ∑ m, (∑ k, c a b k * d k m - ∑ j, c a j m * d b j - ∑ i, c i b m * d a i) • w a b m := by
  simp only [smul_sub, sub_smul, Finset.sum_sub_distrib]
  have t1 : ∑ i, ∑ j, ∑ k, c i j k • ∑ m, d k m • w i j m = ∑ a, ∑ b, ∑ m, (∑ k, c a b k * d k m) • w a b m := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  have t2 : ∑ i, ∑ j, ∑ k, c i j k • ∑ l, d l j • w i l k = ∑ a, ∑ b, ∑ m, (∑ j, c a j m * d b j) • w a b m := by
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans
      (Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm))
  have t3 : ∑ i, ∑ j, ∑ k, c i j k • ∑ l, d l i • w l j k = ∑ a, ∑ b, ∑ m, (∑ i, c i b m * d a i) • w a b m := by
    simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
    calc _ = ∑ i, ∑ b, ∑ a, ∑ m, (c i b m * d a i) • w a b m :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ b, ∑ m, (c i b m * d a i) • w a b m := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ a, ∑ i, ∑ b, ∑ m, (c i b m * d a i) • w a b m := Finset.sum_comm
      _ = ∑ a, ∑ b, ∑ i, ∑ m, (c i b m * d a i) • w a b m := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  rw [t1, t2, t3]

theorem levi_commutator_bracket_part (E : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) :
    (lF E p q * S2 n V - S2 n V * lF E p q : Module.End ℂ (Cn n V)) =
      ∑ a : Pos n, ∑ b : Pos n, ∑ m : Pos n, Dc p q a b m • Wt3 V a b m := by
  have h : (lF E p q * S2 n V - S2 n V * lF E p q : Module.End ℂ (Cn n V)) =
      ∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n, tc i j k • (lF E p q * Wt3 V i j k - Wt3 V i j k * lF E p q) := by
    simp only [S2, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, smul_sub,
      Finset.sum_sub_distrib]
  rw [h]
  simp only [term2]
  exact reindex tc (adC p q) (Wt3 V)

theorem levi_commutator_linear_part (E : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) :
    (lF E p q * S1 E - S1 E * lF E p q : Module.End ℂ (Cn n V)) =
      ∑ l : Pos n, (lift n (E p q * E l.1.1 l.1.2 - E l.1.1 l.1.2 * E p q - ∑ k : Pos n, adC p q l k • E k.1.1 k.1.2) :
        Module.End ℂ (Cn n V)) * ann l := by
  have h : ∀ l : Pos n, (lF E p q * ((lift n (E l.1.1 l.1.2) : Module.End ℂ (Cn n V)) * ann l) -
      (lift n (E l.1.1 l.1.2) : Module.End ℂ (Cn n V)) * ann l * lF E p q : Module.End ℂ (Cn n V)) =
      (lift n (E p q * E l.1.1 l.1.2 - E l.1.1 l.1.2 * E p q) : Module.End ℂ (Cn n V)) * ann l -
        ∑ i : Pos n, adC p q i l • ((lift n (E l.1.1 l.1.2) : Module.End ℂ (Cn n V)) * ann i) := by
    intro l
    have h1 := lF_lift E p q (E l.1.1 l.1.2)
    have h2 := lF_ann E p q l
    rw [← h1]
    have h3 : (∑ i : Pos n, adC p q i l • ((lift n (E l.1.1 l.1.2) : Module.End ℂ (Cn n V)) * ann i)) =
        (lift n (E l.1.1 l.1.2) : Module.End ℂ (Cn n V)) * ∑ i : Pos n, adC p q i l • ann i := by
      simp only [Finset.mul_sum, mul_smul_comm]
    rw [h3, eq_neg_of_add_eq_zero_left (show (∑ i : Pos n, adC p q i l • ann i) + (lF E p q * ann l - ann l * lF E p q) = 0 by rw [h2]; abel)]
    noncomm_ring
  have h0 : (lF E p q * S1 E - S1 E * lF E p q : Module.End ℂ (Cn n V)) =
      ∑ l : Pos n, (lF E p q * ((lift n (E l.1.1 l.1.2) : Module.End ℂ (Cn n V)) * ann l) -
      (lift n (E l.1.1 l.1.2) : Module.End ℂ (Cn n V)) * ann l * lF E p q) := by
    simp only [S1, Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]
  rw [h0, Finset.sum_congr rfl fun l _ => h l, Finset.sum_sub_distrib, Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [lift_sub (n := n) (E p q * E l.1.1 l.1.2 - E l.1.1 l.1.2 * E p q), sub_mul, lift_sum, Finset.sum_mul]
  simp only [lift_smul, smul_mul_assoc]

section Coeff

variable {lev : Fin n → ℕ} {p q : Fin n}

theorem lt_of_lev (hm : Monotone lev) {s t : Fin n} (h : lev s < lev t) : s < t := by
  by_contra hc
  exact absurd (hm (not_lt.1 hc)) (not_le.2 h)

def cX (p q : Fin n) (a b m : Pos n) : ℂ :=
  if a.1.2 = b.1.1 ∧ q = a.1.1 ∧ m.1.1 = p ∧ m.1.2 = b.1.2 then 1 else 0

def cY (p q : Fin n) (a b m : Pos n) : ℂ :=
  if a.1.2 = b.1.1 ∧ b.1.2 = p ∧ m.1.1 = a.1.1 ∧ m.1.2 = q then 1 else 0

def cZ (p q : Fin n) (a b m : Pos n) : ℂ :=
  if a.1.2 = p ∧ q = b.1.1 ∧ m.1.1 = a.1.1 ∧ m.1.2 = b.1.2 then 1 else 0

theorem adC_eq (p q : Fin n) (i k : Pos n) : adC p q i k =
    (if q = i.1.1 ∧ k.1.1 = p ∧ k.1.2 = i.1.2 then 1 else 0) - (if i.1.2 = p ∧ k.1.1 = i.1.1 ∧ k.1.2 = q then 1 else 0) := by
  simp only [adC, Prod.ext_iff]

theorem levi_bracket_sum_first (a b m : Pos n) : ∑ k : Pos n, tc a b k * adC p q k m = cX p q a b m - cY p q a b m := by
  by_cases h : a.1.2 = b.1.1
  · have hlt : a.1.1 < b.1.2 := lt_trans a.2 (h ▸ b.2)
    rw [Finset.sum_eq_single (⟨(a.1.1, b.1.2), hlt⟩ : Pos n)]
    · have : tc a b (⟨(a.1.1, b.1.2), hlt⟩ : Pos n) = 1 := if_pos ⟨h, rfl, rfl⟩
      rw [this, one_mul, adC_eq, cX, cY]
      simp [h]
    · intro k _ hk
      rw [tc, if_neg, zero_mul]
      rintro ⟨-, e1, e2⟩
      exact hk (Subtype.ext (Prod.ext e1 e2))
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [cX, cY, h]
    · intro k _
      simp [tc, h]

theorem levi_bracket_sum_second (hm : Monotone lev) (hpq : lev p = lev q) {a b : Pos n} (ha : inU lev a) (hb : inU lev b) (m : Pos n) :
    ∑ j : Pos n, tc a j m * adC p q b j = cZ p q a b m - cY p q a b m := by
  have hz : (∀ j : Pos n, tc a j m = 0) → ∑ j : Pos n, tc a j m * adC p q b j = 0 := fun h =>
    Finset.sum_eq_zero fun j _ => by rw [h, zero_mul]
  by_cases h1 : m.1.1 = a.1.1
  · by_cases hlt : a.1.2 < m.1.2
    · rw [Finset.sum_eq_single (⟨(a.1.2, m.1.2), hlt⟩ : Pos n)]
      · have : tc a (⟨(a.1.2, m.1.2), hlt⟩ : Pos n) m = 1 := if_pos ⟨rfl, h1, rfl⟩
        rw [this, one_mul, adC_eq, cZ, cY]
        simp only [h1, true_and, and_true]
        congr 1
        · refine if_congr ?_ rfl rfl
          constructor
          · rintro ⟨e1, e2, e3⟩
            exact ⟨e2, e1, e3⟩
          · rintro ⟨e1, e2, e3⟩
            exact ⟨e2, e1, e3⟩
        · refine if_congr ?_ rfl rfl
          constructor
          · rintro ⟨e1, e2, e3⟩
            exact ⟨e2, e1, e3⟩
          · rintro ⟨e1, e2, e3⟩
            exact ⟨e2, e1, e3⟩
      · intro j _ hj
        rw [tc, if_neg, zero_mul]
        rintro ⟨e1, -, e2⟩
        exact hj (Subtype.ext (Prod.ext e1.symm e2.symm))
      · simp
    · rw [hz, cZ, cY, if_neg, if_neg, sub_zero]
      · rintro ⟨e1, e2, -, e3⟩
        refine hlt (lt_of_lev hm ?_)
        rw [e1, e3, ← hpq, ← e2]
        exact hb
      · rintro ⟨e1, e2, -, e3⟩
        refine hlt (lt_of_lev hm ?_)
        rw [e1, hpq, e2, e3]
        exact hb
      · intro j
        rw [tc, if_neg]
        rintro ⟨e1, -, e2⟩
        exact hlt (by rw [e1, e2]; exact j.2)
  · rw [hz, cZ, cY, if_neg, if_neg, sub_zero]
    · exact fun c => h1 c.2.2.1
    · exact fun c => h1 c.2.2.1
    · intro j
      rw [tc, if_neg]
      exact fun c => h1 c.2.1

theorem levi_bracket_sum_third (hm : Monotone lev) (hpq : lev p = lev q) {a b : Pos n} (ha : inU lev a) (hb : inU lev b) (m : Pos n) :
    ∑ i : Pos n, tc i b m * adC p q a i = cX p q a b m - cZ p q a b m := by
  have hz : (∀ i : Pos n, tc i b m = 0) → ∑ i : Pos n, tc i b m * adC p q a i = 0 := fun h =>
    Finset.sum_eq_zero fun i _ => by rw [h, zero_mul]
  by_cases h1 : m.1.2 = b.1.2
  · by_cases hlt : m.1.1 < b.1.1
    · rw [Finset.sum_eq_single (⟨(m.1.1, b.1.1), hlt⟩ : Pos n)]
      · have : tc (⟨(m.1.1, b.1.1), hlt⟩ : Pos n) b m = 1 := if_pos ⟨rfl, rfl, h1⟩
        rw [this, one_mul, adC_eq, cX, cZ]
        simp only [h1, and_true]
        congr 1
        · refine if_congr ?_ rfl rfl
          constructor
          · rintro ⟨e1, e2, e3⟩
            exact ⟨e3.symm, e1, e2⟩
          · rintro ⟨e1, e2, e3⟩
            exact ⟨e2, e3, e1.symm⟩
        · refine if_congr ?_ rfl rfl
          constructor
          · rintro ⟨e1, e2, e3⟩
            exact ⟨e1, e3.symm, e2⟩
          · rintro ⟨e1, e2, e3⟩
            exact ⟨e1, e3, e2.symm⟩
      · intro i _ hi
        rw [tc, if_neg, zero_mul]
        rintro ⟨e1, e2, -⟩
        exact hi (Subtype.ext (Prod.ext e2.symm e1))
      · simp
    · rw [hz, cX, cZ, if_neg, if_neg, sub_zero]
      · rintro ⟨e1, e2, e3, -⟩
        refine hlt (lt_of_lev hm ?_)
        rw [e3, ← e2, ← hpq, ← e1]
        exact ha
      · rintro ⟨e1, e2, e3, -⟩
        refine hlt (lt_of_lev hm ?_)
        rw [e3, hpq, e2, ← e1]
        exact ha
      · intro i
        rw [tc, if_neg]
        rintro ⟨e1, e2, -⟩
        exact hlt (by rw [e2, ← e1]; exact i.2)
  · rw [hz, cX, cZ, if_neg, if_neg, sub_zero]
    · exact fun c => h1 c.2.2.2
    · exact fun c => h1 c.2.2.2
    · intro i
      rw [tc, if_neg]
      exact fun c => h1 c.2.2

theorem Dc_eq_zero (hm : Monotone lev) (hpq : lev p = lev q) {a b : Pos n} (ha : inU lev a) (hb : inU lev b) (m : Pos n) :
    Dc p q a b m = 0 := by
  rw [Dc, levi_bracket_sum_first, levi_bracket_sum_second hm hpq ha hb, levi_bracket_sum_third hm hpq ha hb]
  ring

theorem sum_ind {M : Type*} [AddCommGroup M] [Module ℂ M] {u v : Fin n} (h : u < v) (f : Pos n → M) :
    ∑ k : Pos n, (if k.1.1 = u ∧ k.1.2 = v then (1 : ℂ) else 0) • f k = f ⟨(u, v), h⟩ := by
  rw [Finset.sum_eq_single (⟨(u, v), h⟩ : Pos n)]
  · simp
  · intro k _ hk
    rw [if_neg, zero_smul]
    rintro ⟨e1, e2⟩
    exact hk (Subtype.ext (Prod.ext e1 e2))
  · simp

theorem lin_zero (hm : Monotone lev) (hpq : lev p = lev q) {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E)
    {l : Pos n} (hl : inU lev l) :
    E p q * E l.1.1 l.1.2 - E l.1.1 l.1.2 * E p q - ∑ k : Pos n, adC p q l k • E k.1.1 k.1.2 = 0 := by
  have h1 : ∑ k : Pos n, (if q = l.1.1 ∧ k.1.1 = p ∧ k.1.2 = l.1.2 then (1 : ℂ) else 0) • E k.1.1 k.1.2 =
      if q = l.1.1 then E p l.1.2 else 0 := by
    by_cases h : q = l.1.1
    · have hlt : p < l.1.2 := lt_of_lev hm (by rw [hpq, h]; exact hl)
      simp only [h, true_and, if_true]
      exact sum_ind hlt fun k => E k.1.1 k.1.2
    · simp [h]
  have h2 : ∑ k : Pos n, (if l.1.2 = p ∧ k.1.1 = l.1.1 ∧ k.1.2 = q then (1 : ℂ) else 0) • E k.1.1 k.1.2 =
      if l.1.2 = p then E l.1.1 q else 0 := by
    by_cases h : l.1.2 = p
    · have hlt : l.1.1 < q := lt_of_lev hm (by rw [← hpq, ← h]; exact hl)
      simp only [h, true_and, if_true]
      exact sum_ind hlt fun k => E k.1.1 k.1.2
    · simp [h]
  simp only [adC_eq, sub_smul, Finset.sum_sub_distrib]
  rw [h1, h2, hE p q l.1.1 l.1.2, sub_self]

end Coeff

theorem ann_eq_zero {P : Pos n → Prop} {x : Cn n V} (hx : SuppIn P x) {i : Pos n} (hi : ¬P i) : ann i x = 0 := by
  funext A
  by_contra h
  exact hi (hx _ (CompanionTheory.D.LK.ann_ne h).2 i (mem_insert_self _ _))

theorem ann_supp {P : Pos n → Prop} {x : Cn n V} (hx : SuppIn P x) (i : Pos n) : SuppIn P (ann i x) := by
  intro A h j hj
  exact hx _ (CompanionTheory.D.LK.ann_ne h).2 j (mem_insert_of_mem hj)

theorem lF_bd : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), Monotone lev → GlRel E → ∀ (x : Cn n V), SuppIn (inU lev) x →
    ∀ p q, lev p = lev q → lF E p q (bd (allT n) E x) = bd (allT n) E (lF E p q x) := by
  intro n lev V _ _ E hm hE x hx p q hpq
  have h1 : (lF E p q * S1 E - S1 E * lF E p q : Module.End ℂ (Cn n V)) x = 0 := by
    rw [levi_commutator_linear_part, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : inU lev l
    · rw [lin_zero hm hpq hE hl]
      refine funext fun A => ?_
      simp
    · rw [Module.End.mul_apply, ann_eq_zero hx hl, map_zero]
  have h2 : (lF E p q * S2 n V - S2 n V * lF E p q : Module.End ℂ (Cn n V)) x = 0 := by
    rw [levi_commutator_bracket_part]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun m _ => ?_
    by_cases ha : inU lev a
    · by_cases hb : inU lev b
      · rw [Dc_eq_zero hm hpq ha hb, zero_smul]
      · simp only [Wt3, Module.End.mul_apply]
        rw [ann_eq_zero (ann_supp hx a) hb, map_zero, smul_zero]
    · simp only [Wt3, Module.End.mul_apply]
      rw [ann_eq_zero hx ha, map_zero, map_zero, smul_zero]
  rw [bd_eq]
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h1 h2
  simp only [LinearMap.add_apply, map_add]
  rw [sub_eq_zero.1 h1, sub_eq_zero.1 h2]

end GlobalTheory.CompanionTheory.RgCOBlock.LeviBd
