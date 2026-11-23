import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.OrderedCreationCommutesPastLevi

noncomputable section

namespace GlobalTheory.CompanionTheory.RgCOBlock.LetterGl

open Finset
open Formalism.REAL (GlRel)
open CompanionTheory.D.LK (Pos Cn ann cre lift)
open CompanionTheory.RgExh.U
open GlobalTheory.CompanionTheory.FarReg.BdProd (adL_cre)

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem lift_mul_cre (φ : Module.End ℂ V) (g : Pos n) :
    (lift n φ * cre g : Module.End ℂ (Cn n V)) = cre g * lift n φ :=
  LinearMap.ext fun x => CompanionTheory.D.LK.lift_cre φ g x

theorem lift_mul_ann (φ : Module.End ℂ V) (g : Pos n) :
    (lift n φ * ann g : Module.End ℂ (Cn n V)) = ann g * lift n φ :=
  LinearMap.ext fun x => CompanionTheory.D.LK.lift_ann φ g x

theorem lift_mul_adL (φ : Module.End ℂ V) (p q : Fin n) :
    (lift n φ * adL p q : Module.End ℂ (Cn n V)) = adL p q * lift n φ := by
  simp only [adL, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, lift_mul_cre, mul_assoc, lift_mul_ann, mul_assoc]

theorem term_ann (k i g : Pos n) :
    (ann g * (cre k * ann i) - cre k * ann i * ann g : Module.End ℂ (Cn n V)) = if k = g then ann i else 0 := by
  have h1 := CompanionTheory.D.LK.Car.ann_cre (V := V) g k
  have h2 := CompanionTheory.D.LK.Car.ann_ann (V := V) g i
  rw [← mul_assoc, eq_sub_of_add_eq h1, sub_mul, mul_assoc (cre k) (ann g), eq_neg_of_add_eq_zero_left h2]
  by_cases e : k = g
  · subst e
    simp [mul_assoc]
  · have e' : ¬g = k := fun h => e h.symm
    simp [e, e', mul_assoc]

theorem adL_ann (p q : Fin n) (g : Pos n) :
    (∑ i : Pos n, adC p q i g • ann i : Module.End ℂ (Cn n V)) = ann g * adL p q - adL p q * ann g := by
  have h : (ann g * adL p q - adL p q * ann g : Module.End ℂ (Cn n V)) =
      ∑ i : Pos n, ∑ k : Pos n, adC p q i k • (ann g * (cre k * ann i) - cre k * ann i * ann g) := by
    simp only [adL, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_sub,
      ← Finset.sum_sub_distrib]
  rw [h]
  simp only [term_ann]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single g]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

theorem adL_comm (p q r v : Fin n) :
    (adL p q * adL r v - adL r v * adL p q : Module.End ℂ (Cn n V)) =
      ∑ i : Pos n, ∑ l : Pos n,
        (∑ k : Pos n, (adC r v i k * adC p q k l - adC p q i k * adC r v k l)) • (cre l * ann i) := by
  have gen : ∀ A : Module.End ℂ (Cn n V), A * adL r v - adL r v * A =
      ∑ i : Pos n, ∑ k : Pos n, adC r v i k • (A * (cre k * ann i) - cre k * ann i * A) := by
    intro A
    simp only [adL, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_sub,
      ← Finset.sum_sub_distrib]
  have h1 : ∀ k i : Pos n, (adL p q * (cre k * ann i) - cre k * ann i * adL p q : Module.End ℂ (Cn n V)) =
      (∑ l : Pos n, adC p q k l • cre l) * ann i - cre k * ∑ m : Pos n, adC p q m i • ann m := by
    intro k i
    rw [← adL_cre, adL_ann]
    noncomm_ring
  rw [gen]
  simp only [h1, smul_sub, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, Finset.smul_sum, smul_smul, sub_smul, Finset.sum_smul]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_comm
  · refine (Finset.sum_congr rfl fun k _ => Finset.sum_comm).trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_comm.trans ?_
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]

def dl (a b : Fin n) : ℂ := if a = b then 1 else 0

def cc (p q : Fin n) (s t : Fin n × Fin n) : ℂ :=
  dl q s.1 * dl t.1 p * dl t.2 s.2 - dl s.2 p * dl t.1 s.1 * dl t.2 q

theorem ite3 (A B C : Prop) [Decidable A] [Decidable B] [Decidable C] :
    (if A ∧ B ∧ C then 1 else 0 : ℂ) = (if A then 1 else 0) * (if B then 1 else 0) * (if C then 1 else 0) := by
  by_cases a : A <;> by_cases b : B <;> by_cases c : C <;> simp [a, b, c]

theorem adC_eq (p q : Fin n) (i k : Pos n) : adC p q i k = cc p q i.1 k.1 := by
  have e1 : ∀ a b : Fin n × Fin n, a = b ↔ a.1 = b.1 ∧ a.2 = b.2 := fun a b => Prod.ext_iff
  simp only [adC, cc, dl, e1 k.1, ite3]

theorem ite_dl (a b : Fin n) (x : ℂ) : (if a = b then x else 0) = dl a b * x := by
  by_cases h : a = b <;> simp [dl, h]

theorem sum_at (f : Fin n × Fin n → ℂ) (s : Fin n × Fin n) (hs : (s.1 : ℕ) < s.2) :
    ∑ k : Pos n, (if k.1 = s then f k.1 else 0) = f s := by
  have e : ∀ k : Pos n, k.1 = s ↔ k = ⟨s, hs⟩ := fun k => (Subtype.ext_iff (a1 := k) (a2 := ⟨s, hs⟩)).symm
  simp only [e, Finset.sum_ite_eq', mem_univ, if_true]

theorem sum_adC {lev : Fin n → ℕ} (hm : Monotone lev) {p q : Fin n} (hpq : lev p = lev q) {i : Pos n}
    (hi : inU lev i) (f : Fin n × Fin n → ℂ) :
    ∑ k : Pos n, adC p q i k * f k.1 =
      dl q i.1.1 * f (p, i.1.2) - dl i.1.2 p * f (i.1.1, q) := by
  have a1 : ∑ k : Pos n, (if q = i.1.1 ∧ k.1 = (p, i.1.2) then 1 else 0) * f k.1 = dl q i.1.1 * f (p, i.1.2) := by
    by_cases h : q = i.1.1
    · have hs : (p : ℕ) < i.1.2 := by
        have : lev p < lev i.1.2 := by rw [hpq, h]; exact hi
        exact hm.reflect_lt this
      have := sum_at f (p, i.1.2) hs
      simp only [h, true_and, dl, if_true, one_mul, ite_mul, zero_mul] at this ⊢
      exact this
    · simp [h, dl]
  have a2 : ∑ k : Pos n, (if i.1.2 = p ∧ k.1 = (i.1.1, q) then 1 else 0) * f k.1 = dl i.1.2 p * f (i.1.1, q) := by
    by_cases h : i.1.2 = p
    · have hs : (i.1.1 : ℕ) < q := by
        have : lev i.1.1 < lev q := by rw [← hpq, ← h]; exact hi
        exact hm.reflect_lt this
      have := sum_at f (i.1.1, q) hs
      simp only [h, true_and, dl, if_true, one_mul, ite_mul, zero_mul] at this ⊢
      exact this
    · simp [h, dl]
  simp only [adC, sub_mul, Finset.sum_sub_distrib, a1, a2]

theorem mat_id {lev : Fin n → ℕ} (hm : Monotone lev) {p q r v : Fin n} (hpq : lev p = lev q) (hrv : lev r = lev v)
    {i : Pos n} (hi : inU lev i) (l : Pos n) :
    ∑ k : Pos n, (adC r v i k * adC p q k l - adC p q i k * adC r v k l) =
      (if q = r then adC p v i l else 0) - (if v = p then adC r q i l else 0) := by
  have h1 := sum_adC hm hrv hi (fun s => cc p q s l.1)
  have h2 := sum_adC hm hpq hi (fun s => cc r v s l.1)
  simp only [← adC_eq] at h1 h2
  rw [Finset.sum_sub_distrib, h1, h2, ite_dl, ite_dl]
  simp only [adC_eq, cc]
  ring

theorem ann_eq_zero {lev : Fin n → ℕ} {x : Cn n V} (hx : SuppIn (inU lev) x) {i : Pos n} (hi : ¬inU lev i) :
    ann i x = 0 := by
  funext A
  by_contra h
  exact hi (hx _ (CompanionTheory.D.LK.ann_ne h).2 i (mem_insert_self _ _))

theorem adL_comm_apply {lev : Fin n → ℕ} (hm : Monotone lev) {x : Cn n V} (hx : SuppIn (inU lev) x)
    {p q r v : Fin n} (hpq : lev p = lev q) (hrv : lev r = lev v) :
    adL p q (adL r v x) - adL r v (adL p q x) =
      (if q = r then adL p v x else 0) - (if v = p then adL r q x else 0) := by
  have h := LinearMap.congr_fun (adL_comm (V := V) p q r v) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [h]
  have e : ∀ a b : Fin n, (adL a b x : Cn n V) = ∑ i : Pos n, ∑ l : Pos n, adC a b i l • cre l (ann i x) := by
    intro a b
    simp [adL, LinearMap.sum_apply, Module.End.mul_apply]
  have t : ∀ i l : Pos n,
      (∑ k : Pos n, (adC r v i k * adC p q k l - adC p q i k * adC r v k l)) • cre l (ann i x) =
      ((if q = r then adC p v i l else 0) - (if v = p then adC r q i l else 0)) • cre l (ann i x) := by
    intro i l
    by_cases hi : inU lev i
    · rw [mat_id hm hpq hrv hi]
    · rw [ann_eq_zero hx hi, map_zero, smul_zero, smul_zero]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
  simp only [t]
  simp only [sub_smul, Finset.sum_sub_distrib]
  congr 1
  · split_ifs
    · rw [e]
    · simp
  · split_ifs
    · rw [e]
    · simp

end GlobalTheory.CompanionTheory.RgCOBlock.LetterGl

open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

namespace GlobalTheory.CompanionTheory.RgCOBlock

theorem lF_glRel : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), Monotone lev → GlRel E → ∀ (x : Cn n V), SuppIn (inU lev) x → ∀ p q r v, lev p = lev q → lev r = lev v → lF E p q (lF E r v x) - lF E r v (lF E p q x) = (if q = r then lF E p v x else 0) - (if v = p then lF E r q x else 0) := by
  intro n lev V _ _ E hm hE x hx p q r v hpq hrv
  have hA := LetterGl.adL_comm_apply hm hx hpq hrv
  have h1 : ∀ y : Cn n V, lift n (E p q) (adL r v y) = adL r v (lift n (E p q) y) := fun y =>
    LinearMap.congr_fun (LetterGl.lift_mul_adL (E p q) r v) y
  have h2 : ∀ y : Cn n V, lift n (E r v) (adL p q y) = adL p q (lift n (E r v) y) := fun y =>
    LinearMap.congr_fun (LetterGl.lift_mul_adL (E r v) p q) y
  have hL : lift n (E p q) (lift n (E r v) x) - lift n (E r v) (lift n (E p q) x) =
      (if q = r then lift n (E p v) x else 0) - (if v = p then lift n (E r q) x else 0) := by
    funext A
    have := LinearMap.congr_fun (hE p q r v) (x A)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
    simp only [Pi.sub_apply, CompanionTheory.D.LK.lift_apply]
    rw [this]
    split_ifs <;> simp
  simp only [lF, LinearMap.add_apply, map_add, h1, h2]
  calc _ = (lift n (E p q) (lift n (E r v) x) - lift n (E r v) (lift n (E p q) x)) +
        (adL p q (adL r v x) - adL r v (adL p q x)) := by abel
    _ = _ := by
      rw [hL, hA]
      split_ifs <;> abel

end GlobalTheory.CompanionTheory.RgCOBlock
