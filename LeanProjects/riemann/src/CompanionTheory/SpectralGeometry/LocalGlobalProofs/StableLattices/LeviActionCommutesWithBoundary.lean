import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CanonicalAnticommutationRelationsConsequenceStatement

open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.LeviChain

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

abbrev tau (lev : Fin n → ℕ) (a b : Fin n) : Prop := a < b ∧ lev a < lev b

def cT (lev : Fin n → ℕ) (a b : Fin n) : Module.End ℂ (Cn n V) :=
  if h : tau lev a b then ann ⟨(a, b), h.1⟩ else 0

def dT (lev : Fin n → ℕ) (a b : Fin n) : Module.End ℂ (Cn n V) :=
  if h : tau lev a b then cre ⟨(a, b), h.1⟩ else 0

abbrev LT (E : Fin n → Fin n → Module.End ℂ V) (a b : Fin n) : Module.End ℂ (Cn n V) := lift n (E a b)

theorem cT_pos {lev : Fin n → ℕ} {a b : Fin n} (h : tau lev a b) :
    (cT lev a b : Module.End ℂ (Cn n V)) = ann ⟨(a, b), h.1⟩ := dif_pos h

theorem dT_pos {lev : Fin n → ℕ} {a b : Fin n} (h : tau lev a b) :
    (dT lev a b : Module.End ℂ (Cn n V)) = cre ⟨(a, b), h.1⟩ := dif_pos h

theorem cT_neg {lev : Fin n → ℕ} {a b : Fin n} (h : ¬tau lev a b) :
    (cT lev a b : Module.End ℂ (Cn n V)) = 0 := dif_neg h

theorem dT_neg {lev : Fin n → ℕ} {a b : Fin n} (h : ¬tau lev a b) :
    (dT lev a b : Module.End ℂ (Cn n V)) = 0 := dif_neg h

def SU (V : Type) [AddCommGroup V] [Module ℂ V] (lev : Fin n → ℕ) : Submodule ℂ (Cn n V) where
  carrier := {x | SuppIn (inU lev) x}
  add_mem' := by
    intro x y hx hy A h i hi
    by_cases hxA : x A = 0
    · exact hy A (fun e => h (by simp [hxA, e])) i hi
    · exact hx A hxA i hi
  zero_mem' := fun A h => absurd rfl h
  smul_mem' := fun c x hx A h i hi => hx A (fun e => h (by simp [e])) i hi

variable {lev : Fin n → ℕ} {x : Cn n V}

theorem ann_mem (i : Pos n) (hx : x ∈ SU V lev) : ann i x ∈ SU V lev :=
  fun A hA j hj => hx _ (CompanionTheory.D.LK.ann_ne hA).2 j (mem_insert_of_mem hj)

theorem ann_zero {i : Pos n} (hi : ¬inU lev i) (hx : x ∈ SU V lev) : ann i x = 0 := by
  funext A
  by_contra h
  exact hi (hx _ (CompanionTheory.D.LK.ann_ne h).2 i (mem_insert_self _ _))

theorem cre_mem {i : Pos n} (hi : inU lev i) (hx : x ∈ SU V lev) : cre i x ∈ SU V lev := by
  intro A hA j hj
  by_cases e : j = i
  · exact e ▸ hi
  · exact hx _ (CompanionTheory.D.LK.cre_ne hA).2 j (mem_erase.2 ⟨e, hj⟩)

theorem lift_mem (T : Module.End ℂ V) (hx : x ∈ SU V lev) : lift n T x ∈ SU V lev :=
  fun A hA j hj => hx A (fun e => hA (by simp [e])) j hj

theorem cT_mem (a b : Fin n) (hx : x ∈ SU V lev) : cT lev a b x ∈ SU V lev := by
  by_cases h : tau lev a b
  · rw [cT_pos h]; exact ann_mem _ hx
  · rw [cT_neg h]; exact zero_mem _

theorem dT_mem (a b : Fin n) (hx : x ∈ SU V lev) : dT lev a b x ∈ SU V lev := by
  by_cases h : tau lev a b
  · rw [dT_pos h]; exact cre_mem (i := ⟨(a, b), h.1⟩) h.2 hx
  · rw [dT_neg h]; exact zero_mem _

theorem sum_pos {M : Type*} [AddCommMonoid M] (g : Fin n → Fin n → M) (h : ∀ a b, ¬a < b → g a b = 0) :
    ∑ a, ∑ b, g a b = ∑ i : Pos n, g i.1.1 i.1.2 := by
  rw [← Fintype.sum_prod_type' (f := g),
    ← Finset.sum_filter_of_ne (s := univ) (f := fun y : Fin n × Fin n => g y.1 y.2) (p := fun y => y.1 < y.2)
      (fun y _ hy => by_contra fun t => hy (h _ _ t))]
  exact Finset.sum_subtype _ (by simp) _

theorem bd_allT (E : Fin n → Fin n → Module.End ℂ V) (x : Cn n V) :
    bd (allT n) E x = (∑ i : Pos n, lift n (E i.1.1 i.1.2) (ann i x)) +
      ∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n,
        if i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2 then cre k (ann j (ann i x)) else 0 := by
  simp only [bd, LinearMap.add_apply, LinearMap.sum_apply]
  congr 1
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  by_cases h : i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2
  · rw [if_pos h, if_pos ⟨trivial, trivial, h⟩]; rfl
  · rw [if_neg h, if_neg (fun t => h t.2.2)]; rfl

theorem part_one (E : Fin n → Fin n → Module.End ℂ V) (hx : x ∈ SU V lev) :
    ∑ a, ∑ b, LT E a b (cT lev a b x) = ∑ i : Pos n, lift n (E i.1.1 i.1.2) (ann i x) := by
  rw [sum_pos (fun a b => LT E a b (cT lev a b x))
    (fun a b h => by rw [cT_neg (fun t => h t.1)]; simp)]
  refine sum_congr rfl fun i _ => ?_
  by_cases hi : inU lev i
  · rw [cT_pos (lev := lev) (a := i.1.1) (b := i.1.2) ⟨i.2, hi⟩]
  · rw [cT_neg (lev := lev) (a := i.1.1) (b := i.1.2) (fun t => hi t.2), ann_zero hi hx]; simp

theorem tri_sum (hx : x ∈ SU V lev) (i j : Pos n) :
    (∑ k : Pos n, if i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2 then cre k (ann j (ann i x)) else 0) =
      if i.1.2 = j.1.1 then dT lev i.1.1 j.1.2 (cT lev j.1.1 j.1.2 (cT lev i.1.1 i.1.2 x)) else 0 := by
  by_cases h : i.1.2 = j.1.1
  swap
  · rw [if_neg h]; exact sum_eq_zero fun k _ => if_neg (fun t => h t.1)
  rw [if_pos h]
  by_cases hi : inU lev i
  swap
  · rw [ann_zero hi hx, cT_neg (lev := lev) (a := i.1.1) (b := i.1.2) (fun t => hi t.2)]; simp
  by_cases hj : inU lev j
  swap
  · rw [ann_zero hj (ann_mem i hx), cT_neg (lev := lev) (a := j.1.1) (b := j.1.2) (fun t => hj t.2)]; simp
  have hlt : i.1.1 < j.1.2 := lt_trans i.2 (h ▸ j.2)
  have hlv : lev i.1.1 < lev j.1.2 := lt_trans hi (h ▸ hj)
  rw [dT_pos (lev := lev) ⟨hlt, hlv⟩, cT_pos (lev := lev) (a := j.1.1) (b := j.1.2) ⟨j.2, hj⟩,
    cT_pos (lev := lev) (a := i.1.1) (b := i.1.2) ⟨i.2, hi⟩, sum_eq_single ⟨(i.1.1, j.1.2), hlt⟩]
  · rw [if_pos ⟨h, rfl, rfl⟩]
  · intro k _ hk
    rw [if_neg]
    rintro ⟨-, e1, e2⟩
    exact hk (Subtype.ext (Prod.ext e1 e2))
  · simp

theorem part_two (hx : x ∈ SU V lev) :
    ∑ a, ∑ b, ∑ e, dT lev a e (cT lev b e (cT lev a b x)) =
      ∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n,
        if i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2 then cre k (ann j (ann i x)) else 0 := by
  rw [sum_pos (fun a b => ∑ e, dT lev a e (cT lev b e (cT lev a b x)))
    (fun a b h => by rw [cT_neg (fun t => h t.1)]; simp)]
  refine sum_congr rfl fun i _ => ?_
  simp only [tri_sum hx]
  rw [← sum_pos (fun b e => if i.1.2 = b then dT lev i.1.1 e (cT lev b e (cT lev i.1.1 i.1.2 x)) else 0)
    (fun b e h => by
      split_ifs
      · rw [cT_neg (lev := lev) (a := b) (b := e) (fun t => h t.1)]; simp
      · rfl),
    sum_eq_single i.1.2 (fun b _ hb => sum_eq_zero fun e _ => if_neg (Ne.symm hb)) (by simp)]
  exact sum_congr rfl fun e _ => (if_pos rfl).symm

def Dl (lev : Fin n → ℕ) (E : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ (Cn n V) :=
  (∑ a, ∑ b, LT E a b * cT lev a b) + ∑ a, ∑ b, ∑ e, dT lev a e * cT lev b e * cT lev a b

def Th (lev : Fin n → ℕ) (E : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) : Module.End ℂ (Cn n V) :=
  LT E p q + (∑ r, dT lev p r * cT lev q r - ∑ r, dT lev r q * cT lev r p)

theorem Dl_apply (E : Fin n → Fin n → Module.End ℂ V) (x : Cn n V) :
    Dl lev E x = (∑ a, ∑ b, LT E a b (cT lev a b x)) + ∑ a, ∑ b, ∑ e, dT lev a e (cT lev b e (cT lev a b x)) := by
  simp only [Dl, LinearMap.add_apply, LinearMap.sum_apply, Module.End.mul_apply]

theorem Th_apply (E : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) (x : Cn n V) :
    Th lev E p q x = LT E p q x + (∑ r, dT lev p r (cT lev q r x) - ∑ r, dT lev r q (cT lev r p x)) := by
  simp only [Th, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.sum_apply, Module.End.mul_apply]

theorem bd_eq (E : Fin n → Fin n → Module.End ℂ V) (hx : x ∈ SU V lev) : bd (allT n) E x = Dl lev E x := by
  rw [Dl_apply, bd_allT, part_one E hx, part_two hx]

theorem Dl_mem (E : Fin n → Fin n → Module.End ℂ V) (hx : x ∈ SU V lev) : Dl lev E x ∈ SU V lev := by
  rw [Dl_apply]
  exact add_mem (sum_mem fun a _ => sum_mem fun b _ => lift_mem _ (cT_mem a b hx))
    (sum_mem fun a _ => sum_mem fun b _ => sum_mem fun e _ => dT_mem a e (cT_mem b e (cT_mem a b hx)))

theorem Th_mem (E : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) (hx : x ∈ SU V lev) :
    Th lev E p q x ∈ SU V lev := by
  rw [Th_apply]
  exact add_mem (lift_mem _ hx) (sub_mem (sum_mem fun r _ => dT_mem p r (cT_mem q r hx))
    (sum_mem fun r _ => dT_mem r q (cT_mem r p hx)))

theorem ad_one (hm : Monotone lev) {p q : Fin n} (hpq : lev p = lev q) (hx : x ∈ SU V lev) :
    ∑ i : Pos n, ∑ k : Pos n, (if q = i.1.1 ∧ k.1 = (p, i.1.2) then (1 : ℂ) else 0) • cre k (ann i x) =
      ∑ r, dT lev p r (cT lev q r x) := by
  have e1 : ∑ r, dT lev p r (cT lev q r x) =
      ∑ a, ∑ b, if q = a then dT lev p b (cT lev a b x) else 0 := by
    rw [sum_eq_single q (fun a _ ha => sum_eq_zero fun b _ => if_neg (Ne.symm ha)) (by simp)]
    exact sum_congr rfl fun r _ => (if_pos rfl).symm
  rw [e1, sum_pos (fun a b => if q = a then dT lev p b (cT lev a b x) else 0)
    (fun a b h => by
      split_ifs
      · rw [cT_neg (lev := lev) (a := a) (b := b) (fun t => h t.1)]; simp
      · rfl)]
  refine sum_congr rfl fun i _ => ?_
  by_cases h : q = i.1.1
  swap
  · rw [if_neg h]
    exact sum_eq_zero fun k _ => by rw [if_neg (fun t => h t.1), zero_smul]
  rw [if_pos h]
  by_cases hi : inU lev i
  swap
  · rw [ann_zero hi hx, cT_neg (lev := lev) (a := i.1.1) (b := i.1.2) (fun t => hi t.2)]; simp
  have hlv : lev p < lev i.1.2 := by rw [hpq, h]; exact hi
  have hlt : p < i.1.2 := hm.reflect_lt hlv
  rw [dT_pos (lev := lev) ⟨hlt, hlv⟩, cT_pos (lev := lev) (a := i.1.1) (b := i.1.2) ⟨i.2, hi⟩,
    sum_eq_single ⟨(p, i.1.2), hlt⟩]
  · rw [if_pos ⟨h, rfl⟩, one_smul]
  · intro k _ hk
    rw [if_neg, zero_smul]
    rintro ⟨-, e⟩
    exact hk (Subtype.ext e)
  · simp

theorem ad_two (hm : Monotone lev) {p q : Fin n} (hpq : lev p = lev q) (hx : x ∈ SU V lev) :
    ∑ i : Pos n, ∑ k : Pos n, (if i.1.2 = p ∧ k.1 = (i.1.1, q) then (1 : ℂ) else 0) • cre k (ann i x) =
      ∑ r, dT lev r q (cT lev r p x) := by
  have e1 : ∑ r, dT lev r q (cT lev r p x) =
      ∑ a, ∑ b, if b = p then dT lev a q (cT lev a b x) else 0 := by
    refine sum_congr rfl fun a _ => ?_
    rw [sum_eq_single p (fun b _ hb => if_neg hb) (by simp)]
    exact (if_pos rfl).symm
  rw [e1, sum_pos (fun a b => if b = p then dT lev a q (cT lev a b x) else 0)
    (fun a b h => by
      split_ifs
      · rw [cT_neg (lev := lev) (a := a) (b := b) (fun t => h t.1)]; simp
      · rfl)]
  refine sum_congr rfl fun i _ => ?_
  by_cases h : i.1.2 = p
  swap
  · rw [if_neg h]
    exact sum_eq_zero fun k _ => by rw [if_neg (fun t => h t.1), zero_smul]
  rw [if_pos h]
  by_cases hi : inU lev i
  swap
  · rw [ann_zero hi hx, cT_neg (lev := lev) (a := i.1.1) (b := i.1.2) (fun t => hi t.2)]; simp
  have hlv : lev i.1.1 < lev q := by rw [← hpq, ← h]; exact hi
  have hlt : i.1.1 < q := hm.reflect_lt hlv
  rw [dT_pos (lev := lev) ⟨hlt, hlv⟩, cT_pos (lev := lev) (a := i.1.1) (b := i.1.2) ⟨i.2, hi⟩,
    sum_eq_single ⟨(i.1.1, q), hlt⟩]
  · rw [if_pos ⟨h, rfl⟩, one_smul]
  · intro k _ hk
    rw [if_neg, zero_smul]
    rintro ⟨-, e⟩
    exact hk (Subtype.ext e)
  · simp

theorem lF_eq (hm : Monotone lev) (E : Fin n → Fin n → Module.End ℂ V) {p q : Fin n} (hpq : lev p = lev q)
    (hx : x ∈ SU V lev) : lF E p q x = Th lev E p q x := by
  rw [Th_apply, ← ad_one hm hpq hx, ← ad_two hm hpq hx]
  simp only [lF, adL, adC, sub_smul, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, Module.End.mul_apply, Finset.sum_sub_distrib]

theorem glRel_LT {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (p q a b : Fin n) :
    LT E p q * LT E a b - LT E a b * LT E p q =
      (if q = a then LT E p b else 0) - (if b = p then LT E a q else 0) := by
  refine LinearMap.ext fun y => funext fun A => ?_
  have e := LinearMap.congr_fun (hE p q a b) (y A)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at e
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply, CompanionTheory.D.LK.lift_apply]
  rw [e]
  split_ifs <;> simp

end GlobalTheory.CompanionTheory.LeviChain

open GlobalTheory.CompanionTheory.LeviChain in

theorem GlobalTheory.CompanionTheory.LeviChain.lF_bd_comm : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V),
    Monotone lev → GlRel E → ∀ p q : Fin n, lev p = lev q → ∀ x : Cn n V, SuppIn (inU lev) x →
      lF E p q (bd (allT n) E x) = bd (allT n) E (lF E p q x) := by
  intro n lev V _ _ E hm hE p q hpq x hx
  have hx' : x ∈ SU V lev := hx
  have hc := GlobalTheory.T.canonical_anticommutation_relations_consequence n (Module.End ℂ (Cn n V)) (tau lev) (cT lev) (dT lev) (LT E) p q
    (fun a b a' b' => by
      by_cases h : tau lev a b
      · by_cases h' : tau lev a' b'
        · rw [cT_pos h, cT_pos h']; exact CompanionTheory.D.LK.Car.ann_ann _ _
        · rw [cT_neg h']; simp
      · rw [cT_neg h]; simp)
    (fun a b a' b' => by
      by_cases h : tau lev a b
      · by_cases h' : tau lev a' b'
        · rw [dT_pos h, dT_pos h']; exact CompanionTheory.D.LK.Car.cre_cre _ _
        · rw [dT_neg h']; simp
      · rw [dT_neg h]; simp)
    (fun a b a' b' => by
      by_cases h : tau lev a b
      · by_cases h' : tau lev a' b'
        · rw [cT_pos h, dT_pos h', CompanionTheory.D.LK.Car.ann_cre]
          by_cases e : a = a' ∧ b = b'
          · obtain ⟨rfl, rfl⟩ := e
            simp [h]
          · rw [if_neg, if_neg]
            · exact fun t => e ⟨t.1, t.2.1⟩
            · intro t
              have := congrArg Subtype.val t
              simp only [Prod.mk.injEq] at this
              exact e this
        · rw [dT_neg h', if_neg]
          · simp
          · rintro ⟨rfl, rfl, t⟩
            exact h' t
      · rw [cT_neg h, if_neg (fun t => h t.2.2)]; simp)
    (fun a b h => cT_neg h) (fun a b h => dT_neg h)
    (fun b => ⟨fun h => ⟨hm.reflect_lt (by rw [← hpq] at *; exact h.2), by rw [← hpq]; exact h.2⟩,
      fun h => ⟨hm.reflect_lt (by rw [hpq]; exact h.2), by rw [hpq]; exact h.2⟩⟩)
    (fun a => ⟨fun h => ⟨hm.reflect_lt (by rw [← hpq]; exact h.2), by rw [← hpq]; exact h.2⟩,
      fun h => ⟨hm.reflect_lt (by rw [hpq]; exact h.2), by rw [hpq]; exact h.2⟩⟩)
    (fun a b a' b' => by
      by_cases h : tau lev a' b'
      · rw [cT_pos h]
        exact LinearMap.ext fun y => CompanionTheory.D.LK.lift_ann _ _ y
      · rw [cT_neg h]; exact Commute.zero_right _)
    (fun a b a' b' => by
      by_cases h : tau lev a' b'
      · rw [dT_pos h]
        exact LinearMap.ext fun y => CompanionTheory.D.LK.lift_cre _ _ y
      · rw [dT_neg h]; exact Commute.zero_right _)
    (fun a b => glRel_LT hE p q a b)
  rw [bd_eq E hx', lF_eq hm E hpq (Dl_mem E hx'), lF_eq hm E hpq hx', bd_eq E (Th_mem E p q hx')]
  exact LinearMap.congr_fun hc.eq x
