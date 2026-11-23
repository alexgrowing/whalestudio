import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Finset

namespace GlobalTheory.SignedHC

def entries (S : SPar) : Finset ℚ := S.image Prod.fst

def IsRegular (S : SPar) : Prop := ∀ x ∈ S, ∀ y ∈ S, x.1 = y.1 → x.2 = y.2

instance (S : SPar) : Decidable (IsRegular S) := by unfold IsRegular; infer_instance

def ofSign (E : Finset ℚ) (sg : ℚ → Bool) : SPar := E.image fun x => (x, sg x)

def plus (E : Finset ℚ) : SPar := E.image fun x => (x, true)

def sign (S : SPar) (x : ℚ) : Bool := decide ((x, true) ∈ S)

def nPlus (S : SPar) : ℕ := (S.filter fun x => x.2 = true).card

def nMinus (S : SPar) : ℕ := (S.filter fun x => x.2 = false).card

def signature (S : SPar) : ℕ × ℕ := (nPlus S, nMinus S)

def InCoset (h : ℚ) (E : Finset ℚ) : Prop := ∀ x ∈ E, ∃ z : ℤ, x = h + z

def IsHC (n : ℕ) (S : SPar) : Prop := IsRegular S ∧ S.card = n ∧ InCoset (((n : ℚ) - 1) / 2) (entries S)

def shift (h : ℚ) (S : SPar) : SPar := S.image fun x => (x.1 + h, x.2)

def negate (S : SPar) : SPar := S.image fun x => (-x.1, x.2)

def flip (S : SPar) : SPar := S.image fun x => (x.1, !x.2)

theorem mem_entries {S : SPar} {x : ℚ} : x ∈ entries S ↔ ∃ s, (x, s) ∈ S := by
  simp [entries]

theorem fst_mem_entries {S : SPar} {x : ℚ × Bool} (h : x ∈ S) : x.1 ∈ entries S := mem_image_of_mem _ h

theorem mem_ofSign {E : Finset ℚ} {sg : ℚ → Bool} {x : ℚ × Bool} : x ∈ ofSign E sg ↔ x.1 ∈ E ∧ x.2 = sg x.1 := by
  obtain ⟨a, s⟩ := x
  simp only [ofSign, mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨y, hy, rfl, rfl⟩; exact ⟨hy, rfl⟩
  · rintro ⟨h, rfl⟩; exact ⟨a, h, rfl, rfl⟩

@[simp] theorem mem_plus {E : Finset ℚ} {x : ℚ × Bool} : x ∈ plus E ↔ x.1 ∈ E ∧ x.2 = true :=
  mem_ofSign (sg := fun _ => true)

theorem mem_shift {h : ℚ} {S : SPar} {x : ℚ × Bool} : x ∈ shift h S ↔ (x.1 - h, x.2) ∈ S := by
  simp only [shift, mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩; simpa using hy
  · intro hx; exact ⟨_, hx, by simp⟩

theorem mem_negate {S : SPar} {x : ℚ × Bool} : x ∈ negate S ↔ (-x.1, x.2) ∈ S := by
  simp only [negate, mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩; simpa using hy
  · intro hx; exact ⟨_, hx, by simp⟩

theorem mem_flip {S : SPar} {x : ℚ × Bool} : x ∈ flip S ↔ (x.1, !x.2) ∈ S := by
  simp only [flip, mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩; simpa using hy
  · intro hx; exact ⟨_, hx, by simp⟩

@[simp] theorem shift_zero (S : SPar) : shift 0 S = S := by
  ext x; simp [mem_shift]

@[simp] theorem entries_union (S T : SPar) : entries (S ∪ T) = entries S ∪ entries T := image_union _ _

@[simp] theorem entries_ofSign (E : Finset ℚ) (sg : ℚ → Bool) : entries (ofSign E sg) = E := by
  ext x; simp [mem_entries, mem_ofSign]

@[simp] theorem entries_plus (E : Finset ℚ) : entries (plus E) = E := entries_ofSign E fun _ => true

theorem plus_union (E E' : Finset ℚ) : plus (E ∪ E') = plus E ∪ plus E' := image_union _ _

@[simp] theorem plus_empty : plus ∅ = ∅ := rfl

theorem isRegular_ofSign (E : Finset ℚ) (sg : ℚ → Bool) : IsRegular (ofSign E sg) := by
  intro x hx y hy h
  rw [(mem_ofSign.1 hx).2, (mem_ofSign.1 hy).2, h]

theorem isRegular_plus (E : Finset ℚ) : IsRegular (plus E) := isRegular_ofSign E fun _ => true

theorem IsRegular.sign_eq {S : SPar} (h : IsRegular S) {x : ℚ × Bool} (hx : x ∈ S) : sign S x.1 = x.2 := by
  obtain ⟨a, s⟩ := x
  cases s
  · simp only [sign, decide_eq_false_iff_not]
    intro h'
    simpa using h _ hx _ h' rfl
  · simpa [sign] using hx

theorem IsRegular.eq_ofSign {S : SPar} (h : IsRegular S) : S = ofSign (entries S) (sign S) := by
  ext x
  rw [mem_ofSign]
  constructor
  · intro hx; exact ⟨fst_mem_entries hx, (h.sign_eq hx).symm⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨s, hs⟩ := mem_entries.1 h1
    have := h.sign_eq hs
    have e : x = (x.1, s) := Prod.ext rfl (by simp only at this ⊢; rw [h2, this])
    rw [e]; exact hs

theorem isRegular_iff {S : SPar} : IsRegular S ↔ ∃ E sg, S = ofSign E sg :=
  ⟨fun h => ⟨_, _, h.eq_ofSign⟩, by rintro ⟨E, sg, rfl⟩; exact isRegular_ofSign E sg⟩

theorem IsRegular.card_entries {S : SPar} (h : IsRegular S) : (entries S).card = S.card :=
  card_image_of_injOn fun x hx y hy e => Prod.ext e (h x hx y hy e)

theorem isRegular_iff_card {S : SPar} : IsRegular S ↔ (entries S).card = S.card :=
  ⟨IsRegular.card_entries, fun h _ hx _ hy e => congrArg Prod.snd (card_image_iff.1 h hx hy e)⟩

theorem IsRegular.union {S T : SPar} (hS : IsRegular S) (hT : IsRegular T) (h : Disjoint (entries S) (entries T)) :
    IsRegular (S ∪ T) := by
  intro x hx y hy e
  rcases mem_union.1 hx with hx | hx <;> rcases mem_union.1 hy with hy | hy
  · exact hS x hx y hy e
  · exact absurd (e ▸ fst_mem_entries hy) (disjoint_left.1 h (fst_mem_entries hx))
  · exact absurd (e ▸ fst_mem_entries hx) (disjoint_left.1 h (fst_mem_entries hy))
  · exact hT x hx y hy e

theorem nPlus_add_nMinus (S : SPar) : nPlus S + nMinus S = S.card := by
  unfold nPlus nMinus
  rw [← card_filter_add_card_filter_not (s := S) (fun x => x.2 = true)]
  simp

@[simp] theorem nMinus_plus (E : Finset ℚ) : nMinus (plus E) = 0 := by
  simp only [nMinus, card_eq_zero, filter_eq_empty_iff, mem_plus]
  rintro x ⟨-, h⟩; simp [h]

@[simp] theorem nPlus_plus (E : Finset ℚ) : nPlus (plus E) = E.card := by
  have := nPlus_add_nMinus (plus E)
  rw [nMinus_plus, ← (isRegular_plus E).card_entries, entries_plus] at this
  exact this

def descList (E : Finset ℚ) : List ℚ := E.sort (· ≥ ·)

def descEnum {n : ℕ} (E : Finset ℚ) (h : E.card = n) : Fin n → ℚ := fun i => E.orderEmbOfFin h i.rev

def highestWeight {n : ℕ} (E : Finset ℚ) (h : E.card = n) : Fin n → ℚ :=
  fun i => descEnum E h i - (((n : ℚ) - 1) / 2 - ((i : ℕ) : ℚ))

@[simp] theorem mem_descList {E : Finset ℚ} {x : ℚ} : x ∈ descList E ↔ x ∈ E := mem_sort _

theorem pairwise_descList (E : Finset ℚ) : (descList E).Pairwise (· > ·) := (sortedGT_sort E).pairwise

theorem descList_eq {E : Finset ℚ} {L : List ℚ} (hL : L.Pairwise (· > ·)) (h : L.toFinset = E) : descList E = L := by
  subst h
  exact (List.toFinset_sort (· ≥ ·) (hL.imp fun h => ne_of_gt h)).2 (hL.imp fun h => le_of_lt h)

theorem strictAnti_descEnum {n : ℕ} (E : Finset ℚ) (h : E.card = n) : StrictAnti (descEnum E h) :=
  fun _ _ hab => (E.orderEmbOfFin h).strictMono (Fin.rev_lt_rev.2 hab)

theorem descEnum_mem {n : ℕ} (E : Finset ℚ) (h : E.card = n) (i : Fin n) : descEnum E h i ∈ E :=
  orderEmbOfFin_mem _ _ _

theorem image_descEnum {n : ℕ} (E : Finset ℚ) (h : E.card = n) : univ.image (descEnum E h) = E := by
  refine eq_of_subset_of_card_le (fun x hx => ?_) ?_
  · obtain ⟨i, -, rfl⟩ := mem_image.1 hx; exact descEnum_mem E h i
  · rw [card_image_of_injective _ (strictAnti_descEnum E h).injective]; simp [h]

theorem descEnum_unique {n : ℕ} {E : Finset ℚ} (h : E.card = n) {f : Fin n → ℚ} (hf : StrictAnti f) (hm : ∀ i, f i ∈ E) :
    descEnum E h = f := by
  have := orderEmbOfFin_unique h (f := fun i => f i.rev) (fun i => hm _) fun a b hab => hf (Fin.rev_lt_rev.2 hab)
  funext i
  simp only [descEnum, ← this, Fin.rev_rev]

theorem highestWeight_int {n : ℕ} {E : Finset ℚ} (h : E.card = n) (hE : InCoset (((n : ℚ) - 1) / 2) E) (i : Fin n) :
    ∃ z : ℤ, highestWeight E h i = z := by
  obtain ⟨z, hz⟩ := hE _ (descEnum_mem E h i)
  exact ⟨z + (i : ℕ), by simp only [highestWeight, hz]; push_cast; ring⟩

theorem highestWeight_antitone {n : ℕ} {E : Finset ℚ} (h : E.card = n) {c : ℚ} (hE : InCoset c E) :
    Antitone (highestWeight E h) := by
  cases n with
  | zero => intro a; exact a.elim0
  | succ n =>
    refine Fin.antitone_iff_succ_le.2 fun i => ?_
    obtain ⟨z, hz⟩ := hE _ (descEnum_mem E h i.succ)
    obtain ⟨w, hw⟩ := hE _ (descEnum_mem E h i.castSucc)
    have hlt := strictAnti_descEnum E h (Fin.castSucc_lt_succ (i := i))
    rw [hz, hw] at hlt
    have h1 : z < w := by exact_mod_cast (by linarith : (z : ℚ) < w)
    have h2 : (z : ℚ) + 1 ≤ w := by exact_mod_cast h1
    simp only [highestWeight, hz, hw, Fin.val_succ, Fin.val_castSucc]
    push_cast
    linarith

theorem goodPar_iff {n p q : ℕ} {S : SPar} : GoodPar n p q S ↔ IsHC n S ∧ signature S = (p, q) := by
  have key : ∀ (f : Fin n → ℚ) (ε : Fin n → Bool), Function.Injective f → ∀ s : Bool,
      ((univ.image fun a => (f a, ε a)).filter fun x => x.2 = s).card = (univ.filter fun a => ε a = s).card := by
    intro f ε hf s
    rw [filter_image, card_image_of_injective _ fun a b h => hf (congrArg Prod.fst h)]
  constructor
  · rintro ⟨lam, ε, ⟨hanti, f, hf, rfl⟩, hHC, hp, hq⟩
    have hinj : Function.Injective f := fun a b h => hanti.injective (by rw [hf, hf, h])
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro x hx y hy e
      obtain ⟨a, -, rfl⟩ := mem_image.1 hx
      obtain ⟨b, -, rfl⟩ := mem_image.1 hy
      rw [hinj e]
    · rw [card_image_of_injective _ fun a b h => hinj (congrArg Prod.fst h)]; simp
    · intro x hx
      obtain ⟨s, hs⟩ := mem_entries.1 hx
      obtain ⟨a, -, e⟩ := mem_image.1 hs
      obtain ⟨z, hz⟩ := hHC.2 a
      refine ⟨z, ?_⟩
      have e1 : f a = x := congrArg Prod.fst e
      rw [hf, e1] at hz
      have : ((x : ℚ) : ℝ) = ((((n : ℚ) - 1) / 2 + z : ℚ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · simp only [signature, nPlus, nMinus, key f ε hinj, hp, hq]
  · rintro ⟨⟨hreg, hcard, hco⟩, hsig⟩
    have hc : (entries S).card = n := hreg.card_entries.trans hcard
    have hS : S = univ.image fun a => (descEnum _ hc a, sign S (descEnum _ hc a)) := by
      conv_lhs => rw [hreg.eq_ofSign, ← image_descEnum _ hc, ofSign, image_image]
      rfl
    have hanti : StrictAnti fun a => ((descEnum _ hc a : ℚ) : ℝ) :=
      fun a b h => by simpa using strictAnti_descEnum _ hc h
    refine ⟨fun a => (descEnum _ hc a : ℝ), fun a => sign S (descEnum _ hc a), ⟨hanti, _, fun _ => rfl, hS⟩,
      ⟨hanti, fun a => ?_⟩, ?_, ?_⟩
    · obtain ⟨z, hz⟩ := hco _ (descEnum_mem _ hc a)
      exact ⟨z, by simp only [hz]; push_cast; ring⟩
    · rw [← key _ _ (strictAnti_descEnum _ hc).injective, ← hS]; exact congrArg Prod.fst hsig
    · rw [← key _ _ (strictAnti_descEnum _ hc).injective, ← hS]; exact congrArg Prod.snd hsig

def ncDists (S : SPar) : Finset ℚ := ((S ×ˢ S).filter fun x => x.1.2 ≠ x.2.2).image fun x => |x.1.1 - x.2.1|

def ncGap (S : SPar) : WithTop ℚ := (ncDists S).min

theorem mem_ncDists {S : SPar} {d : ℚ} : d ∈ ncDists S ↔ ∃ x ∈ S, ∃ y ∈ S, x.2 ≠ y.2 ∧ |x.1 - y.1| = d := by
  simp only [ncDists, mem_image, mem_filter, mem_product]
  constructor
  · rintro ⟨x, ⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨_, h1, _, h2, h3, h4⟩
  · rintro ⟨x, h1, y, h2, h3, h4⟩; exact ⟨(x, y), ⟨⟨h1, h2⟩, h3⟩, h4⟩

theorem le_ncGap_iff {S : SPar} {h : ℚ} :
    (h : WithTop ℚ) ≤ ncGap S ↔ ∀ x ∈ S, ∀ y ∈ S, x.2 ≠ y.2 → h ≤ |x.1 - y.1| := by
  rw [ncGap, Finset.le_min_iff]
  simp only [mem_ncDists, WithTop.coe_le_coe]
  exact ⟨fun H x hx y hy hs => H _ ⟨x, hx, y, hy, hs, rfl⟩, by rintro H _ ⟨x, hx, y, hy, hs, rfl⟩; exact H x hx y hy hs⟩

theorem ncGap_eq_top_iff {S : SPar} : ncGap S = ⊤ ↔ ∀ x ∈ S, ∀ y ∈ S, x.2 = y.2 := by
  rw [ncGap, Finset.min_eq_top, eq_empty_iff_forall_notMem]
  simp only [mem_ncDists]
  exact ⟨fun H x hx y hy => by_contra fun hs => H _ ⟨x, hx, y, hy, hs, rfl⟩,
    by rintro H _ ⟨x, hx, y, hy, hs, -⟩; exact hs (H x hx y hy)⟩

theorem ncGap_eq_coe_iff {S : SPar} {g : ℚ} : ncGap S = (g : WithTop ℚ) ↔
    (∃ x ∈ S, ∃ y ∈ S, x.2 ≠ y.2 ∧ |x.1 - y.1| = g) ∧ ∀ x ∈ S, ∀ y ∈ S, x.2 ≠ y.2 → g ≤ |x.1 - y.1| := by
  rw [← mem_ncDists, ← le_ncGap_iff]
  exact ⟨fun h => ⟨mem_of_min h, h.ge⟩, fun h => le_antisymm (min_le h.1) h.2⟩

theorem lt_ncGap_iff {S : SPar} {h : ℚ} :
    (h : WithTop ℚ) < ncGap S ↔ ∀ x ∈ S, ∀ y ∈ S, x.2 ≠ y.2 → h < |x.1 - y.1| := by
  constructor
  · intro H x hx y hy hs
    have := H.trans_le (min_le (mem_ncDists.2 ⟨x, hx, y, hy, hs, rfl⟩))
    exact_mod_cast this
  · intro H
    cases hg : ncGap S with
    | top => exact WithTop.coe_lt_top _
    | coe g =>
      obtain ⟨⟨x, hx, y, hy, hs, rfl⟩, -⟩ := ncGap_eq_coe_iff.1 hg
      exact_mod_cast H x hx y hy hs

@[simp] theorem ncGap_plus (E : Finset ℚ) : ncGap (plus E) = ⊤ :=
  ncGap_eq_top_iff.2 fun _ hx _ hy => by rw [(mem_plus.1 hx).2, (mem_plus.1 hy).2]

theorem mem_block {c x : ℚ} {t : ℕ} : x ∈ TPar.block c t ↔ ∃ a : ℕ, a < t ∧ x = c + ((t : ℚ) - 1) / 2 - a := by
  simp only [TPar.block, mem_image, mem_range]
  exact ⟨fun ⟨a, h, e⟩ => ⟨a, h, e.symm⟩, fun ⟨a, h, e⟩ => ⟨a, h, e.symm⟩⟩

@[simp] theorem card_block (c : ℚ) (t : ℕ) : (TPar.block c t).card = t := by
  rw [TPar.block, card_image_of_injective, card_range]
  intro a b h
  have : (a : ℚ) = b := by simp only at h; linarith
  exact_mod_cast this

theorem abs_sub_le_of_mem_block {c x : ℚ} {t : ℕ} (h : x ∈ TPar.block c t) : |x - c| ≤ ((t : ℚ) - 1) / 2 := by
  obtain ⟨a, ha, rfl⟩ := mem_block.1 h
  have h1 : (a : ℚ) + 1 ≤ t := by exact_mod_cast ha
  have h0 : (0 : ℚ) ≤ a := by positivity
  rw [abs_le]; constructor <;> linarith

theorem neg_mem_block {c x : ℚ} {t : ℕ} : -x ∈ TPar.block (-c) t ↔ x ∈ TPar.block c t := by
  have key : ∀ c x : ℚ, x ∈ TPar.block c t → -x ∈ TPar.block (-c) t := by
    intro c x h
    obtain ⟨a, ha, rfl⟩ := mem_block.1 h
    refine mem_block.2 ⟨t - 1 - a, by omega, ?_⟩
    have : ((t - 1 - a : ℕ) : ℚ) = t - 1 - a := by
      rw [Nat.sub_sub, Nat.cast_sub (by omega)]; push_cast; ring
    rw [this]; ring
  exact ⟨fun h => by simpa using key _ _ h, key _ _⟩

theorem sub_mem_block {c x h : ℚ} {t : ℕ} : x - h ∈ TPar.block c t ↔ x ∈ TPar.block (c + h) t := by
  simp only [mem_block]
  exact exists_congr fun a => and_congr_right fun _ => ⟨fun e => by linarith, fun e => by linarith⟩

theorem inCoset_block (c : ℚ) (t : ℕ) : InCoset (c + ((t : ℚ) + 1) / 2) (TPar.block c t) := by
  intro x hx
  obtain ⟨a, -, rfl⟩ := mem_block.1 hx
  exact ⟨-1 - a, by push_cast; ring⟩

def FarFrom (c d : ℚ) (S : SPar) : Prop := ∀ x ∈ entries S, d ≤ |x - c|

instance (c d : ℚ) (S : SPar) : Decidable (FarFrom c d S) := by unfold FarFrom; infer_instance

def liftPlus (c : ℚ) (t : ℕ) (S : SPar) : SPar :=
  (S.image fun x => (x.1, if x.1 < c then !x.2 else x.2)) ∪ plus (TPar.block c t)

def liftMinus (c : ℚ) (t : ℕ) (S : SPar) : SPar :=
  (S.image fun x => (x.1, if c < x.1 then !x.2 else x.2)) ∪ plus (TPar.block c t)

inductive Orientation

  | pos

  | neg
  deriving DecidableEq

def lift : Orientation → ℚ → ℕ → SPar → SPar
  | .pos => liftPlus
  | .neg => liftMinus

theorem mem_image_change {P : ℚ → Prop} [DecidablePred P] {S : SPar} {x : ℚ × Bool} :
    x ∈ (S.image fun y => (y.1, if P y.1 then !y.2 else y.2)) ↔ (¬ P x.1 ∧ x ∈ S) ∨ (P x.1 ∧ (x.1, !x.2) ∈ S) := by
  rw [mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    by_cases h : P y.1 <;> simp [h, hy]
  · rintro (⟨h, hx⟩ | ⟨h, hx⟩)
    · exact ⟨x, hx, by simp [h]⟩
    · exact ⟨_, hx, by simp [h]⟩

theorem mem_liftPlus {c : ℚ} {t : ℕ} {S : SPar} {x : ℚ × Bool} : x ∈ liftPlus c t S ↔
    (c ≤ x.1 ∧ x ∈ S) ∨ (x.1 < c ∧ (x.1, !x.2) ∈ S) ∨ (x.1 ∈ TPar.block c t ∧ x.2 = true) := by
  rw [liftPlus, mem_union, mem_image_change (P := fun y => y < c), mem_plus, not_lt, or_assoc]

theorem mem_liftMinus {c : ℚ} {t : ℕ} {S : SPar} {x : ℚ × Bool} : x ∈ liftMinus c t S ↔
    (x.1 ≤ c ∧ x ∈ S) ∨ (c < x.1 ∧ (x.1, !x.2) ∈ S) ∨ (x.1 ∈ TPar.block c t ∧ x.2 = true) := by
  rw [liftMinus, mem_union, mem_image_change (P := fun y => c < y), mem_plus, not_lt, or_assoc]

theorem entries_lift (o : Orientation) (c : ℚ) (t : ℕ) (S : SPar) :
    entries (lift o c t S) = entries S ∪ TPar.block c t := by
  cases o <;> simp only [lift, liftPlus, liftMinus, entries_union, entries_plus] <;> congr 1 <;>
    simp only [entries, image_image] <;> rfl

theorem liftMinus_eq_negate (c : ℚ) (t : ℕ) (S : SPar) : liftMinus c t S = negate (liftPlus (-c) t (negate S)) := by
  ext x
  simp only [mem_liftMinus, mem_negate, mem_liftPlus, neg_mem_block, neg_neg, neg_le_neg_iff, neg_lt_neg_iff]

theorem lift_shift (o : Orientation) (c h : ℚ) (t : ℕ) (S : SPar) :
    lift o (c + h) t (shift h S) = shift h (lift o c t S) := by
  ext x
  cases o <;>
    simp only [lift, mem_liftMinus, mem_shift, mem_liftPlus, sub_mem_block, le_sub_iff_add_le, sub_lt_iff_lt_add,
      sub_le_iff_le_add, lt_sub_iff_add_lt]

theorem FarFrom.disjoint_block {c : ℚ} {t : ℕ} {S : SPar} (h : FarFrom c (((t : ℚ) + 1) / 2) S) :
    Disjoint (entries S) (TPar.block c t) := by
  refine disjoint_left.2 fun x hx hb => ?_
  have := h x hx
  have := abs_sub_le_of_mem_block hb
  linarith

theorem IsRegular.lift {S : SPar} (hS : IsRegular S) (o : Orientation) {c : ℚ} {t : ℕ}
    (h : Disjoint (entries S) (TPar.block c t)) : IsRegular (lift o c t S) := by
  have key : ∀ (P : ℚ → Prop) [DecidablePred P],
      IsRegular ((S.image fun y => (y.1, if P y.1 then !y.2 else y.2)) ∪ plus (TPar.block c t)) := by
    intro P _
    refine IsRegular.union ?_ (isRegular_plus _) ?_
    · intro x hx y hy e
      obtain ⟨x, hx', rfl⟩ := mem_image.1 hx
      obtain ⟨y, hy', rfl⟩ := mem_image.1 hy
      have e' : x.1 = y.1 := e
      simp only [e', hS x hx' y hy' e']
    · rw [entries_plus, entries, image_image]; exact h
  cases o
  · exact key fun y => y < c
  · exact key fun y => c < y

theorem IsRegular.card_lift {S : SPar} (hS : IsRegular S) (o : Orientation) {c : ℚ} {t : ℕ}
    (h : Disjoint (entries S) (TPar.block c t)) : (SignedHC.lift o c t S).card = S.card + t := by
  rw [← (hS.lift o h).card_entries, entries_lift, card_union_of_disjoint h, card_block, hS.card_entries]

theorem InCoset.lift {c : ℚ} {t : ℕ} {S : SPar} (h : InCoset (c + ((t : ℚ) + 1) / 2) (entries S)) (o : Orientation) :
    InCoset (c + ((t : ℚ) + 1) / 2) (entries (lift o c t S)) := by
  intro x hx
  rw [entries_lift, mem_union] at hx
  exact hx.elim (h x) (inCoset_block c t x)

theorem nMinus_change (P : ℚ → Prop) [DecidablePred P] (S : SPar) (E : Finset ℚ) :
    nMinus ((S.image fun y => (y.1, if P y.1 then !y.2 else y.2)) ∪ plus E) =
      (S.filter fun x => ¬ P x.1 ∧ x.2 = false).card + (S.filter fun x => P x.1 ∧ x.2 = true).card := by
  rw [← card_union_of_disjoint (disjoint_filter.2 fun x _ h1 h2 => h1.1 h2.1), nMinus]
  symm
  refine card_bij (fun x _ => (x.1, false)) ?_ ?_ ?_
  · rintro ⟨a, s⟩ hx
    simp only [mem_union, mem_filter, mem_image_change (P := P)] at hx ⊢
    rcases hx with ⟨h1, h2, rfl⟩ | ⟨h1, h2, rfl⟩
    · exact ⟨Or.inl (Or.inl ⟨h2, h1⟩), trivial⟩
    · exact ⟨Or.inl (Or.inr ⟨h2, h1⟩), trivial⟩
  · rintro ⟨a, s⟩ hx ⟨a', s'⟩ hy e
    obtain rfl : a = a' := congrArg Prod.fst e
    simp only [mem_union, mem_filter] at hx hy
    rcases hx with ⟨-, h2, rfl⟩ | ⟨-, h2, rfl⟩ <;> rcases hy with ⟨-, h3, rfl⟩ | ⟨-, h3, rfl⟩ <;>
      first | rfl | contradiction
  · rintro ⟨a, s⟩ hx
    simp only [mem_union, mem_filter, mem_image_change (P := P), mem_plus] at hx ⊢
    obtain ⟨h, rfl⟩ := hx
    rcases h with (⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨-, h⟩
    · exact ⟨(a, false), Or.inl ⟨h2, h1, rfl⟩, rfl⟩
    · exact ⟨(a, true), Or.inr ⟨h2, h1, rfl⟩, rfl⟩
    · exact absurd h (by simp)

theorem nMinus_liftPlus (c : ℚ) (t : ℕ) (S : SPar) : nMinus (liftPlus c t S) =
    (S.filter fun x => c ≤ x.1 ∧ x.2 = false).card + (S.filter fun x => x.1 < c ∧ x.2 = true).card := by
  rw [liftPlus, nMinus_change (fun y => y < c)]
  simp only [not_lt]

theorem nMinus_liftMinus (c : ℚ) (t : ℕ) (S : SPar) : nMinus (liftMinus c t S) =
    (S.filter fun x => x.1 ≤ c ∧ x.2 = false).card + (S.filter fun x => c < x.1 ∧ x.2 = true).card := by
  rw [liftMinus, nMinus_change (fun y => c < y)]
  simp only [not_lt]

def ofIx {p q : ℕ} (lam : Ix p q → ℚ) : SPar := univ.image fun a => (lam a, a.isLeft)

theorem mem_ofIx_ofBlocks {p q : ℕ} {l₁ l₂ : List ℚ} (hp : l₁.length = p) (hq : l₂.length = q) {x : ℚ × Bool} :
    x ∈ ofIx (ofBlocks l₁ l₂ : Ix p q → ℚ) ↔ (x.1 ∈ l₁ ∧ x.2 = true) ∨ (x.1 ∈ l₂ ∧ x.2 = false) := by
  subst hp hq
  obtain ⟨a, s⟩ := x
  simp only [ofIx, mem_image, mem_univ, true_and, Sum.exists, ofBlocks, Sum.isLeft_inl, Sum.isLeft_inr, Prod.mk.injEq,
    List.mem_iff_getElem]
  refine or_congr ?_ ?_ <;> constructor
  · rintro ⟨i, rfl, rfl⟩; exact ⟨⟨i, i.2, by simp⟩, rfl⟩
  · rintro ⟨⟨i, hi, rfl⟩, rfl⟩; exact ⟨⟨i, hi⟩, by simp [hi], rfl⟩
  · rintro ⟨i, rfl, rfl⟩; exact ⟨⟨i, i.2, by simp⟩, rfl⟩
  · rintro ⟨⟨i, hi, rfl⟩, rfl⟩; exact ⟨⟨i, hi⟩, by simp [hi], rfl⟩

theorem liftPlus_lamA (t : ℕ) {al be ga de : List ℚ} (hp : ∀ e ∈ al ++ ga, 0 < e) (hn : ∀ e ∈ be ++ de, e < 0) :
    liftPlus 0 t (ofIx (lamA al be ga de)) = ofIx (lamA' t al be ga de) := by
  ext ⟨a, s⟩
  have hb : a ∈ TPar.block 0 t ↔ a ∈ Formalism.BasicNotions.TH.block t := by
    simp [mem_block, Formalism.BasicNotions.TH.block, eq_comm]
  have hl : (Formalism.BasicNotions.TH.block t).length = t := by simp [Formalism.BasicNotions.TH.block]
  simp only [List.mem_append] at hp hn
  have h1 : a ∈ al → 0 < a := fun h => hp a (Or.inl h)
  have h2 : a ∈ ga → 0 < a := fun h => hp a (Or.inr h)
  have h3 : a ∈ be → a < 0 := fun h => hn a (Or.inl h)
  have h4 : a ∈ de → a < 0 := fun h => hn a (Or.inr h)
  rw [mem_liftPlus, lamA, lamA', mem_ofIx_ofBlocks (by simp) (by simp), mem_ofIx_ofBlocks (by simp) (by simp),
    mem_ofIx_ofBlocks (by simp [hl]; omega) (by simp), hb]
  simp only [List.mem_append]
  cases s <;> simp <;> grind

theorem gapGt_iff {p q : ℕ} (lam : Ix p q → ℚ) (h : ℚ) : GapGt lam (h : ℝ) ↔ (h : WithTop ℚ) < ncGap (ofIx lam) := by
  rw [lt_ncGap_iff, GapGt]
  simp only [ofIx, forall_mem_image, mem_univ, true_implies]
  refine forall₂_congr fun a b => imp_congr ?_ ?_
  · cases a <;> cases b <;> simp [sameBlock]
  · rw [← Rat.cast_abs, Rat.cast_lt]

def Adjacent (E : Finset ℚ) (x y : ℚ) : Prop := x ∈ E ∧ y ∈ E ∧ y < x ∧ ∀ z ∈ E, ¬ (y < z ∧ z < x)

theorem isChain_descList_iff {E : Finset ℚ} {R : ℚ → ℚ → Prop} :
    (descList E).IsChain R ↔ ∀ x ∈ E, ∀ y ∈ E, y < x → (∀ z ∈ E, ¬ (y < z ∧ z < x)) → R x y := by
  have hp := List.pairwise_iff_getElem.1 (pairwise_descList E)
  rw [List.isChain_iff_getElem]
  constructor
  · intro H x hx y hy hxy hz
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 (mem_descList.2 hx)
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 (mem_descList.2 hy)
    rcases lt_trichotomy j (i + 1) with h | h | h
    · rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
      · exact absurd (hp j i hj hi h) (not_lt.2 hxy.le)
      · subst h; exact absurd hxy (lt_irrefl _)
    · subst h; exact H i hj
    · exact absurd ⟨hp (i + 1) j (by omega) hj h, hp i (i + 1) hi (by omega) (by omega)⟩
        (hz _ (mem_descList.1 (List.getElem_mem _)))
  · intro H i hi
    refine H _ (mem_descList.1 (List.getElem_mem _)) _ (mem_descList.1 (List.getElem_mem _))
      (hp i (i + 1) (by omega) hi (by omega)) ?_
    rintro z hz ⟨h1, h2⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 (mem_descList.2 hz)
    rcases lt_trichotomy k i with h | h | h
    · exact absurd (hp k i hk (by omega) h) (not_lt.2 h2.le)
    · subst h; exact absurd h2 (lt_irrefl _)
    · rcases (Nat.succ_le_of_lt h).eq_or_lt with h | h
      · subst h; exact absurd h1 (lt_irrefl _)
      · exact absurd (hp (i + 1) k hi hk h) (not_lt.2 h1.le)

inductive Letter

  | plus

  | minus

  | circPlus

  | circMinus
  deriving DecidableEq

instance : Fintype Letter := ⟨{.plus, .minus, .circPlus, .circMinus}, fun x => by cases x <;> simp⟩

def hePairs : List (Letter × Letter) :=
  [(.circPlus, .plus), (.plus, .circPlus), (.minus, .circMinus), (.circMinus, .minus),
    (.plus, .minus), (.minus, .plus), (.circPlus, .circMinus), (.circMinus, .circPlus)]

def HePair (a b : Letter) : Prop := (a, b) ∈ hePairs

instance (a b : Letter) : Decidable (HePair a b) := by unfold HePair; infer_instance

def letter (S T : SPar) (x : ℚ) : Letter :=
  if x ∈ entries S then (if sign S x then .plus else .minus) else (if sign T x then .circPlus else .circMinus)

def word (S T : SPar) : List Letter := (descList (entries S ∪ entries T)).map (letter S T)

def HeInterlace (S T : SPar) : Prop :=
  IsRegular S ∧ IsRegular T ∧ Disjoint (entries S) (entries T) ∧ (word S T).IsChain HePair

theorem HePair.symm : ∀ {a b : Letter}, HePair a b → HePair b a := by decide

def Letter.swap : Letter → Letter
  | .plus => .minus
  | .minus => .plus
  | .circPlus => .circMinus
  | .circMinus => .circPlus

theorem HePair.swap : ∀ {a b : Letter}, HePair a b → HePair a.swap b.swap := by decide

theorem heInterlace_iff {S T : SPar} : HeInterlace S T ↔
    IsRegular S ∧ IsRegular T ∧ Disjoint (entries S) (entries T) ∧
      ∀ x ∈ entries S ∪ entries T, ∀ y ∈ entries S ∪ entries T, y < x →
        (∀ z ∈ entries S ∪ entries T, ¬ (y < z ∧ z < x)) → HePair (letter S T x) (letter S T y) := by
  rw [HeInterlace, word, List.isChain_map, isChain_descList_iff]

instance (S T : SPar) : Decidable (HeInterlace S T) := decidable_of_iff _ heInterlace_iff.symm

theorem word_eq {S T : SPar} {L : List ℚ} (hL : L.Pairwise (· > ·)) (h : L.toFinset = entries S ∪ entries T) :
    word S T = L.map (letter S T) := by
  rw [word, descList_eq hL h]

theorem letter_left {S : SPar} (hS : IsRegular S) (T : SPar) {x : ℚ × Bool} (hx : x ∈ S) :
    letter S T x.1 = if x.2 then .plus else .minus := by
  rw [letter, if_pos (fst_mem_entries hx), hS.sign_eq hx]

theorem letter_right {S T : SPar} (hT : IsRegular T) (h : Disjoint (entries S) (entries T)) {x : ℚ × Bool}
    (hx : x ∈ T) : letter S T x.1 = if x.2 then .circPlus else .circMinus := by
  rw [letter, if_neg (disjoint_right.1 h (fst_mem_entries hx)), hT.sign_eq hx]

theorem HeInterlace.flip {S T : SPar} (h : HeInterlace S T) : HeInterlace (flip S) (flip T) := by
  obtain ⟨hS, hT, hd, hw⟩ := heInterlace_iff.1 h
  have he : ∀ U : SPar, entries (SignedHC.flip U) = entries U := fun U => by
    simp only [entries, SignedHC.flip, image_image]; rfl
  have hr : ∀ U : SPar, IsRegular U → IsRegular (SignedHC.flip U) := fun U hU x hx y hy e => by
    simpa using hU _ (mem_flip.1 hx) _ (mem_flip.1 hy) e
  have hd' : Disjoint (entries (SignedHC.flip S)) (entries (SignedHC.flip T)) := by rwa [he, he]
  have hl : ∀ x ∈ entries S ∪ entries T, letter (SignedHC.flip S) (SignedHC.flip T) x = (letter S T x).swap := by
    intro x hx
    rcases mem_union.1 hx with hx | hx <;> obtain ⟨s, hs⟩ := mem_entries.1 hx
    · rw [letter_left (hr S hS) _ (x := (x, !s)) (mem_flip.2 (by simpa using hs)), letter_left hS T hs]
      cases s <;> rfl
    · rw [letter_right (hr T hT) hd' (x := (x, !s)) (mem_flip.2 (by simpa using hs)), letter_right hT hd hs]
      cases s <;> rfl
  refine heInterlace_iff.2 ⟨hr S hS, hr T hT, hd', ?_⟩
  rw [he, he]
  intro x hx y hy h1 h2
  rw [hl x hx, hl y hy]
  exact (hw x hx y hy h1 h2).swap

theorem HeInterlace.negate {S T : SPar} (h : HeInterlace S T) : HeInterlace (negate S) (negate T) := by
  obtain ⟨hS, hT, hd, hw⟩ := heInterlace_iff.1 h
  have he : ∀ (U : SPar) (x : ℚ), x ∈ entries (SignedHC.negate U) ↔ -x ∈ entries U := fun U x => by
    simp only [mem_entries, mem_negate]
  have hr : ∀ U : SPar, IsRegular U → IsRegular (SignedHC.negate U) := fun U hU x hx y hy e =>
    hU (-x.1, x.2) (mem_negate.1 hx) (-y.1, y.2) (mem_negate.1 hy) (congrArg Neg.neg e)
  have hl : ∀ x, letter (SignedHC.negate S) (SignedHC.negate T) x = letter S T (-x) := fun x => by
    simp [letter, sign, he, mem_negate]
  have hu : ∀ x, x ∈ entries (SignedHC.negate S) ∪ entries (SignedHC.negate T) ↔ -x ∈ entries S ∪ entries T :=
    fun x => by simp only [mem_union, he]
  refine heInterlace_iff.2 ⟨hr S hS, hr T hT,
    disjoint_left.2 fun x h1 h2 => disjoint_left.1 hd ((he _ _).1 h1) ((he _ _).1 h2), ?_⟩
  intro x hx y hy h1 h2
  rw [hl, hl]
  refine (hw _ ((hu y).1 hy) _ ((hu x).1 hx) (neg_lt_neg h1) fun z hz hh => ?_).symm
  exact h2 (-z) ((hu _).2 (by rwa [neg_neg])) ⟨by linarith [hh.2], by linarith [hh.1]⟩

def StrictInterlace (A B : Finset ℚ) : Prop :=
  ∃ (n : ℕ) (a : Fin (n + 1) → ℚ) (b : Fin n → ℚ), A = univ.image a ∧ B = univ.image b ∧
    ∀ i : Fin n, b i < a i.castSucc ∧ a i.succ < b i

theorem strictAnti_of_interlace {n : ℕ} {a : Fin (n + 1) → ℚ} {b : Fin n → ℚ}
    (h : ∀ i : Fin n, b i < a i.castSucc ∧ a i.succ < b i) : StrictAnti a ∧ StrictAnti b := by
  have ha : StrictAnti a := Fin.strictAnti_iff_succ_lt.2 fun i => (h i).2.trans (h i).1
  refine ⟨ha, fun i j hij => ?_⟩
  exact (h j).1.trans_le ((ha.antitone (show i.succ ≤ j.castSucc from hij)).trans (h i).2.le)

theorem strictInterlace_iff_descEnum {n : ℕ} {A B : Finset ℚ} (hA : A.card = n + 1) (hB : B.card = n) :
    StrictInterlace A B ↔ ∀ i : Fin n, descEnum B hB i < descEnum A hA i.castSucc ∧ descEnum A hA i.succ < descEnum B hB i := by
  constructor
  · rintro ⟨n', a, b, rfl, rfl, h⟩
    obtain ⟨ha, hb⟩ := strictAnti_of_interlace h
    have : n' = n := by rw [card_image_of_injective _ hb.injective] at hB; simpa using hB
    subst this
    rw [descEnum_unique hA ha fun i => mem_image_of_mem _ (mem_univ i),
      descEnum_unique hB hb fun i => mem_image_of_mem _ (mem_univ i)]
    exact h
  · intro h
    exact ⟨n, _, _, (image_descEnum A hA).symm, (image_descEnum B hB).symm, h⟩

theorem StrictInterlace.card_eq {A B : Finset ℚ} (h : StrictInterlace A B) : A.card = B.card + 1 := by
  obtain ⟨n, a, b, rfl, rfl, h⟩ := h
  obtain ⟨ha, hb⟩ := strictAnti_of_interlace h
  rw [card_image_of_injective _ ha.injective, card_image_of_injective _ hb.injective]; simp

theorem strictInterlace_iff {A B : Finset ℚ} : StrictInterlace A B ↔
    Disjoint A B ∧ A.Nonempty ∧ (∀ y ∈ B, ∃ x ∈ A, y < x) ∧ (∀ y ∈ B, ∃ x ∈ A, x < y) ∧
      ∀ x ∈ A ∪ B, ∀ y ∈ A ∪ B, y < x → (∀ z ∈ A ∪ B, ¬ (y < z ∧ z < x)) → (x ∈ A ↔ y ∉ A) := by
  constructor
  · rintro ⟨n, a, b, rfl, rfl, h⟩
    obtain ⟨ha, hb⟩ := strictAnti_of_interlace h
    have ma : ∀ i, a i ∈ univ.image a := fun i => mem_image_of_mem _ (mem_univ i)
    have mb : ∀ i, b i ∈ univ.image b := fun i => mem_image_of_mem _ (mem_univ i)
    have hd : Disjoint (univ.image a) (univ.image b) := by
      refine disjoint_left.2 fun x hx hy => ?_
      obtain ⟨i, -, rfl⟩ := mem_image.1 hx
      obtain ⟨j, -, e⟩ := mem_image.1 hy
      rcases le_or_gt i j.castSucc with hij | hij
      · exact absurd ((h j).1.trans_le (ha.antitone hij)) (by rw [e]; exact lt_irrefl _)
      · exact absurd ((ha.antitone (show j.succ ≤ i from hij)).trans_lt (h j).2) (by rw [e]; exact lt_irrefl _)
    refine ⟨hd, ⟨_, ma 0⟩, ?_, ?_, ?_⟩
    · intro y hy; obtain ⟨j, -, rfl⟩ := mem_image.1 hy; exact ⟨_, ma _, (h j).1⟩
    · intro y hy; obtain ⟨j, -, rfl⟩ := mem_image.1 hy; exact ⟨_, ma _, (h j).2⟩
    · intro x hx y hy hxy hz
      constructor
      · intro hxa hya
        obtain ⟨i, -, rfl⟩ := mem_image.1 hxa
        obtain ⟨j, -, rfl⟩ := mem_image.1 hya
        have hij : i < j := ha.lt_iff_gt.1 hxy
        have hi : i.1 < n := by have := j.2; have : i.1 < j.1 := hij; omega
        exact hz (b ⟨i.1, hi⟩) (mem_union_right _ (mb _))
          ⟨(ha.antitone (show (⟨i.1, hi⟩ : Fin n).succ ≤ j from hij)).trans_lt (h _).2, (h ⟨i.1, hi⟩).1⟩
      · intro hya
        by_contra hxa
        obtain ⟨i, -, rfl⟩ := mem_image.1 ((mem_union.1 hx).resolve_left hxa)
        obtain ⟨j, -, rfl⟩ := mem_image.1 ((mem_union.1 hy).resolve_left hya)
        have hij : i < j := hb.lt_iff_gt.1 hxy
        exact hz (a i.succ) (mem_union_left _ (ma _))
          ⟨(h j).1.trans_le (ha.antitone (show i.succ ≤ j.castSucc from hij)), (h i).2⟩
  · rintro ⟨hd, ⟨x0, hx0⟩, htop, hbot, hadj⟩
    have hc := List.isChain_iff_getElem.1 ((isChain_descList_iff (R := fun x y => x ∈ A ↔ y ∉ A)).2 hadj)
    have hp := List.pairwise_iff_getElem.1 (pairwise_descList (A ∪ B))
    have hm : ∀ x, x ∈ A ∪ B ↔ ∃ i, ∃ h : i < (descList (A ∪ B)).length, (descList (A ∪ B))[i] = x :=
      fun x => by rw [← mem_descList, List.mem_iff_getElem]
    generalize descList (A ∪ B) = L at hc hp hm
    obtain ⟨i0, hi0, -⟩ := (hm x0).1 (mem_union_left _ hx0)
    have hin : ∀ i (h : i < L.length), L[i] ∉ A → L[i] ∈ B :=
      fun i h hA => (mem_union.1 ((hm _).2 ⟨i, h, rfl⟩)).resolve_left hA
    have h0 : L[0] ∈ A := by
      by_contra hA
      obtain ⟨x, hx, hlt⟩ := htop _ (hin 0 (by omega) hA)
      obtain ⟨i, hi, rfl⟩ := (hm x).1 (mem_union_left _ hx)
      rcases Nat.eq_zero_or_pos i with rfl | h
      · exact hA hx
      · exact absurd (hp 0 i (by omega) hi h) (not_lt.2 hlt.le)
    have hl : L[L.length - 1] ∈ A := by
      by_contra hA
      obtain ⟨x, hx, hlt⟩ := hbot _ (hin _ (by omega) hA)
      obtain ⟨i, hi, rfl⟩ := (hm x).1 (mem_union_left _ hx)
      rcases (show i ≤ L.length - 1 by omega).eq_or_lt with h | h
      · subst h; exact hA hx
      · exact absurd (hp i _ hi (by omega) h) (not_lt.2 hlt.le)
    have hpar : ∀ i (h : i < L.length), L[i] ∈ A ↔ i % 2 = 0 := by
      intro i
      induction i with
      | zero => intro _; simpa using h0
      | succ i ih =>
        intro h
        have h1 := hc i h
        have h2 := ih (by omega)
        constructor
        · intro h3; by_contra h4; exact (h1.1 (h2.2 (by omega))) h3
        · intro h3; by_contra h4; have := h2.1 (h1.2 h4); omega
    have hodd := (hpar _ (by omega)).1 hl
    refine ⟨L.length / 2, fun i => L[2 * i.1]'(by have := i.2; omega), fun i => L[2 * i.1 + 1]'(by have := i.2; omega),
      ?_, ?_, fun i => ⟨hp _ _ _ _ (by simp), hp _ _ _ _ (by simp; omega)⟩⟩
    · ext x
      simp only [mem_image, mem_univ, true_and]
      constructor
      · intro hx
        obtain ⟨i, hi, rfl⟩ := (hm x).1 (mem_union_left _ hx)
        have := (hpar i hi).1 hx
        exact ⟨⟨i / 2, by omega⟩, by congr 1; simp only; omega⟩
      · rintro ⟨i, rfl⟩; exact (hpar _ _).2 (by omega)
    · ext x
      simp only [mem_image, mem_univ, true_and]
      constructor
      · intro hx
        obtain ⟨i, hi, rfl⟩ := (hm x).1 (mem_union_right _ hx)
        have : ¬ i % 2 = 0 := fun h => disjoint_left.1 hd ((hpar i hi).2 h) hx
        exact ⟨⟨i / 2, by omega⟩, by congr 1; simp only; omega⟩
      · rintro ⟨i, rfl⟩; exact hin _ _ fun h => by have := (hpar _ _).1 h; omega

instance (A B : Finset ℚ) : Decidable (StrictInterlace A B) := decidable_of_iff _ strictInterlace_iff.symm

theorem strictInterlace_iff_he {A B : Finset ℚ} : StrictInterlace A B ↔
    HeInterlace (plus A) (plus B) ∧ A.Nonempty ∧ (∀ y ∈ B, ∃ x ∈ A, y < x) ∧ ∀ y ∈ B, ∃ x ∈ A, x < y := by
  have hl : ∀ x ∈ A ∪ B, letter (plus A) (plus B) x = if x ∈ A then .plus else .circPlus := by
    intro x hx
    by_cases h : x ∈ A
    · simp [letter, sign, h]
    · simp [letter, sign, h, (mem_union.1 hx).resolve_left h]
  have hq : ∀ x ∈ A ∪ B, ∀ y ∈ A ∪ B,
      HePair (letter (plus A) (plus B) x) (letter (plus A) (plus B) y) ↔ (x ∈ A ↔ y ∉ A) := by
    intro x hx y hy
    rw [hl x hx, hl y hy]
    by_cases h : x ∈ A <;> by_cases h' : y ∈ A <;> simp [h, h'] <;> decide
  rw [strictInterlace_iff, heInterlace_iff, entries_plus, entries_plus]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨isRegular_plus _, isRegular_plus _, h1, fun x hx y hy a b => (hq x hx y hy).2 (h5 x hx y hy a b)⟩, h2, h3, h4⟩
  · rintro ⟨⟨-, -, h1, h5⟩, h2, h3, h4⟩
    exact ⟨h1, h2, h3, h4, fun x hx y hy a b => (hq x hx y hy).1 (h5 x hx y hy a b)⟩

structure GridData where

  k : ℕ

  m : ℕ

  t : ℕ

  s : ℕ

  ga : ℕ

  v : ℕ → ℤ

  b : ℕ → ℤ

  e : ℕ → ℤ

  cen : ℕ → ℤ

  two_le_k : 2 ≤ k

  v_anti : ∀ i j, 2 ≤ i → i < j → j ≤ k → v j < v i

  b_mono : ∀ i j, 1 ≤ i → i < j → j ≤ m → b i < b j

namespace GridData

variable (G : GridData)

def r : ℕ := G.k + G.m - 1

def n : ℕ := G.r + 1

def bigN : ℕ := G.k + G.m * (G.t + G.s + 1)

def rankD (i j : ℕ) : ℕ := G.r + j * G.t + i * G.s

def rankP (i : ℕ) : ℕ := G.n + i * (G.s - 1)

def nTop : ℕ := G.n + G.m * (G.s - 1)

def rankX (j : ℕ) : ℕ := G.nTop + j * (G.t + 1)

def spreadBound (abelian₂ : ℚ) : ℚ := ((G.m : ℚ) + 1) * ((G.ga : ℚ) + 1) + abelian₂ + G.nTop

def a (i : ℕ) : ℚ := (G.v 2 : ℚ) + 1 / 2 + ((G.m : ℚ) + 1 - i) * G.ga

def vHalf (i : ℕ) : ℚ := (G.v i : ℚ) - 1 / 2

def mid (i : ℕ) : ℚ := (G.a (i - 1) + G.a i) / 2

def NearMid : Prop := ∀ i ∈ Icc 1 G.m, |(G.cen i : ℚ) - G.mid i| ≤ 1

instance : Decidable G.NearMid := by unfold NearMid; infer_instance

def cloud : Finset ℚ := (Icc 2 G.k).image fun i => (G.v i : ℚ)

def lows : Finset ℚ := (Icc 1 G.m).image fun l => -(G.b l : ℚ)

def cloudHalf : Finset ℚ := (Icc 2 G.k).image G.vHalf

def tops : Finset ℚ := (range (G.m + 1)).image G.a

def blockM (j : ℕ) : Finset ℚ := TPar.block (-(G.e j : ℚ)) G.t

def blockMPlus (j : ℕ) : Finset ℚ := TPar.block (-(G.e j : ℚ)) (G.t + 1)

def blockC (i : ℕ) : Finset ℚ := TPar.block (G.cen i : ℚ) G.s

def blockC' (i : ℕ) : Finset ℚ := TPar.block (G.cen i : ℚ) (G.s - 1)

def lam : SPar :=
  ((range (G.m + 1)).image fun i => (G.a i, decide (Even (G.m - i)))) ∪ plus G.cloudHalf

def parD0 : SPar :=
  plus G.cloud ∪ (Icc 1 G.m).image fun l => (-(G.b l : ℚ), decide (Even (l - 1)))

def parD (i j : ℕ) : SPar :=
  plus G.cloud ∪ ((Icc 1 G.m).image fun l => (-(G.b l : ℚ), decide (l ≤ j + 1 ∨ Even (l - j - 1)))) ∪
    plus ((Icc 1 j).biUnion G.blockM) ∪ plus ((Icc (G.m - i + 1) G.m).biUnion G.blockC)

def parPi (i : ℕ) : SPar :=
  ((range (G.m + 1)).image fun l => (G.a l, decide (G.m - i ≤ l ∨ Even (G.m - i - l)))) ∪ plus G.cloudHalf ∪
    plus ((Icc (G.m - i + 1) G.m).biUnion G.blockC')

def weightX (j : ℕ) : Finset ℚ :=
  entries G.lam ∪ (Icc 1 G.m).biUnion G.blockC' ∪ (Icc 1 j).biUnion G.blockMPlus

def parX (j : ℕ) : SPar := plus (G.weightX j)

theorem n_eq : G.n = G.k + G.m := by have := G.two_le_k; unfold n r; omega

theorem a_m : G.a G.m = G.v 2 + G.ga + 1 / 2 := by unfold a; ring

theorem a_eq_succ_add (i : ℕ) : G.a i = G.a (i + 1) + G.ga := by unfold a; push_cast; ring

theorem a_pred {i : ℕ} (hi : 1 ≤ i) : G.a (i - 1) = G.a i + G.ga := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' hi
  exact G.a_eq_succ_add i

theorem a_sub_a (i j : ℕ) : G.a i - G.a j = ((j : ℚ) - i) * G.ga := by unfold a; ring

theorem mid_eq {i : ℕ} (hi : 1 ≤ i) : G.mid i = G.a i + G.ga / 2 := by rw [mid, G.a_pred hi]; ring

theorem nearMid_of_floor (h : ∀ i ∈ Icc 1 G.m, G.cen i = ⌊G.mid i⌋) : G.NearMid := by
  intro i hi
  have h1 := Int.floor_le (G.mid i)
  have h2 := Int.lt_floor_add_one (G.mid i)
  rw [h i hi, abs_le]; constructor <;> linarith

theorem nearMid_of_ceil (h : ∀ i ∈ Icc 1 G.m, G.cen i = ⌈G.mid i⌉ - 1) : G.NearMid := by
  intro i hi
  have h1 := Int.le_ceil (G.mid i)
  have h2 := Int.ceil_lt_add_one (G.mid i)
  rw [h i hi, abs_le]; push_cast; constructor <;> linarith

variable {G}

theorem mem_cloud {x : ℚ} : x ∈ G.cloud ↔ ∃ i, 2 ≤ i ∧ i ≤ G.k ∧ x = G.v i := by
  simp only [cloud, mem_image, mem_Icc, and_assoc, eq_comm]

theorem mem_lows {x : ℚ} : x ∈ G.lows ↔ ∃ l, 1 ≤ l ∧ l ≤ G.m ∧ x = -(G.b l : ℚ) := by
  simp only [lows, mem_image, mem_Icc, and_assoc, eq_comm]

theorem mem_cloudHalf {x : ℚ} : x ∈ G.cloudHalf ↔ ∃ i, 2 ≤ i ∧ i ≤ G.k ∧ x = G.vHalf i := by
  simp only [cloudHalf, mem_image, mem_Icc, and_assoc, eq_comm]

theorem mem_tops {x : ℚ} : x ∈ G.tops ↔ ∃ i, i ≤ G.m ∧ x = G.a i := by
  simp only [tops, mem_image, mem_range, Nat.lt_succ_iff, eq_comm]

theorem mem_lam {x : ℚ × Bool} : x ∈ G.lam ↔
    (∃ i, i ≤ G.m ∧ x = (G.a i, decide (Even (G.m - i)))) ∨ (x.1 ∈ G.cloudHalf ∧ x.2 = true) := by
  simp only [lam, mem_union, mem_image, mem_range, Nat.lt_succ_iff, mem_plus, eq_comm]

theorem mem_discrete_parameter_iff {x : ℚ × Bool} : x ∈ G.parD0 ↔
    (x.1 ∈ G.cloud ∧ x.2 = true) ∨ ∃ l, 1 ≤ l ∧ l ≤ G.m ∧ x = (-(G.b l : ℚ), decide (Even (l - 1))) := by
  simp only [parD0, mem_union, mem_image, mem_Icc, mem_plus, and_assoc, eq_comm]

theorem mem_parD {i j : ℕ} {x : ℚ × Bool} : x ∈ G.parD i j ↔
    (x.1 ∈ G.cloud ∧ x.2 = true) ∨
    (∃ l, 1 ≤ l ∧ l ≤ G.m ∧ x = (-(G.b l : ℚ), decide (l ≤ j + 1 ∨ Even (l - j - 1)))) ∨
    (∃ l, 1 ≤ l ∧ l ≤ j ∧ x.1 ∈ G.blockM l ∧ x.2 = true) ∨
    (∃ l, G.m - i + 1 ≤ l ∧ l ≤ G.m ∧ x.1 ∈ G.blockC l ∧ x.2 = true) := by
  simp only [parD, mem_union, mem_image, mem_Icc, mem_plus, mem_biUnion, and_assoc, or_assoc, eq_comm,
    ← exists_and_right]

theorem mem_parPi {i : ℕ} {x : ℚ × Bool} : x ∈ G.parPi i ↔
    (∃ l, l ≤ G.m ∧ x = (G.a l, decide (G.m - i ≤ l ∨ Even (G.m - i - l)))) ∨
    (x.1 ∈ G.cloudHalf ∧ x.2 = true) ∨
    (∃ l, G.m - i + 1 ≤ l ∧ l ≤ G.m ∧ x.1 ∈ G.blockC' l ∧ x.2 = true) := by
  simp only [parPi, mem_union, mem_image, mem_range, Nat.lt_succ_iff, mem_Icc, mem_plus, mem_biUnion, and_assoc,
    or_assoc, eq_comm, ← exists_and_right]

variable (G)

theorem entries_lam : entries G.lam = G.tops ∪ G.cloudHalf := by
  rw [lam, entries_union, entries_plus, entries, image_image]; rfl

theorem entries_discrete_parameter : entries G.parD0 = G.cloud ∪ G.lows := by
  rw [parD0, entries_union, entries_plus, entries, image_image]; rfl

theorem entries_parD (i j : ℕ) : entries (G.parD i j) =
    G.cloud ∪ G.lows ∪ (Icc 1 j).biUnion G.blockM ∪ (Icc (G.m - i + 1) G.m).biUnion G.blockC := by
  simp only [parD, entries_union, entries_plus]
  rw [entries, image_image]; rfl

theorem entries_parPi (i : ℕ) : entries (G.parPi i) = entries G.lam ∪ (Icc (G.m - i + 1) G.m).biUnion G.blockC' := by
  simp only [parPi, entries_lam, entries_union, entries_plus]
  rw [entries, image_image]; rfl

variable {G}

theorem mem_weightX {j : ℕ} {x : ℚ} : x ∈ G.weightX j ↔ x ∈ G.tops ∨ x ∈ G.cloudHalf ∨
    (∃ i, 1 ≤ i ∧ i ≤ G.m ∧ x ∈ G.blockC' i) ∨ ∃ l, 1 ≤ l ∧ l ≤ j ∧ x ∈ G.blockMPlus l := by
  simp only [weightX, entries_lam, mem_union, mem_biUnion, mem_Icc, and_assoc, or_assoc]

variable (G)

theorem parPi_zero : G.parPi 0 = G.lam := by
  have h : ∀ l, (G.m ≤ l ∨ Even (G.m - l)) ↔ Even (G.m - l) := fun l =>
    ⟨fun h => h.elim (fun h => by simp [Nat.sub_eq_zero_of_le h]) id, Or.inr⟩
  simp [parPi, lam, h]

theorem parD_zero_zero : G.parD 0 0 = G.parD0 := by
  have h : ∀ l, (l ≤ 1 ∨ Even (l - 1)) ↔ Even (l - 1) := fun l =>
    ⟨fun h => h.elim (fun h => by simp [Nat.sub_eq_zero_of_le h]) id, Or.inr⟩
  simp [parD, parD0, h]

theorem parPi_m : G.parPi G.m = G.parX 0 := by
  simp only [parPi, parX, weightX, entries_lam, plus_union, Nat.sub_self, zero_le, true_or, decide_true, zero_add]
  simp [plus, tops, image_image, Function.comp_def]

theorem weightX_succ (j : ℕ) : G.weightX (j + 1) = G.weightX j ∪ G.blockMPlus (j + 1) := by
  rw [weightX, weightX, ← Finset.insert_Icc_right_eq_Icc_add_one (by omega), biUnion_insert, union_assoc _ _ (G.blockMPlus _),
    union_comm (G.blockMPlus _)]

theorem dpar_eq {D : D7} (P : TPar D) (τ : D.what₂.Tau) (hk : G.k = D.R.k) (hm : G.m = D.R.m) (ht : G.t = P.t)
    (hv : ∀ i, P.v τ i = G.v (i.1 + 2)) (hb : ∀ l, P.b τ l = G.b (l.1 + 1)) (he : ∀ l, P.e τ l = G.e (l.1 + 1))
    {j : ℕ} (hj : j ≤ G.m) : P.Dpar j τ = shift (if Odd j then P.eta τ else 0) (G.parD 0 j) := by
  unfold TPar.Dpar shift
  congr 1
  ext x
  rw [mem_parD]
  simp only [mem_union, mem_image, mem_biUnion, mem_filter, mem_univ, true_and, hv, hb, he, mem_cloud, blockM, ht,
    or_assoc]
  refine or_congr ?_ (or_congr ?_ ?_)
  · constructor
    · rintro ⟨i, rfl⟩; exact ⟨⟨i.1 + 2, by omega, by have := i.2; omega, rfl⟩, rfl⟩
    · rintro ⟨⟨i, h1, h2, h3⟩, h4⟩
      exact ⟨⟨i - 2, by omega⟩, Prod.ext (by rw [h3]; simp only [Nat.sub_add_cancel h1]) h4.symm⟩
  · have hs : ∀ l : ℕ, decide (l ≤ j ∨ Even (l - j)) = decide (l + 1 ≤ j + 1 ∨ Even (l + 1 - j - 1)) := fun l => by
      rw [show l + 1 - j - 1 = l - j by omega]; simp
    constructor
    · rintro ⟨l, rfl⟩; exact ⟨l.1 + 1, by omega, by have := l.2; omega, by rw [hs]⟩
    · rintro ⟨l, h1, h2, rfl⟩
      exact ⟨⟨l - 1, by omega⟩, by rw [hs]; simp only [Nat.sub_add_cancel h1]⟩
  · constructor
    · rintro ⟨l, hl, y, hy, rfl⟩; exact Or.inl ⟨l.1 + 1, by omega, by omega, hy, rfl⟩
    · rintro (⟨l, h1, h2, h3, h4⟩ | ⟨l, h1, h2, -⟩)
      · exact ⟨⟨l - 1, by omega⟩, by simp only; omega, x.1, by simpa only [Nat.sub_add_cancel h1] using h3,
          Prod.ext rfl h4.symm⟩
      · omega

def extend {n : ℕ} (d : ℕ) (f : Fin n → ℚ) (i : ℕ) : ℤ := if h : i - d < n then ⌊f ⟨i - d, h⟩⌋ else 0

theorem extend_cast {n : ℕ} (d : ℕ) {f : Fin n → ℚ} (hf : ∀ i, ∃ z : ℤ, f i = z) (i : Fin n) :
    (extend d f (i.1 + d) : ℚ) = f i := by
  obtain ⟨z, hz⟩ := hf i
  simp [extend, hz]

def ofHCParam {R : Ranks} (P : HCParam R) (s ga : ℕ) (cen : ℕ → ℤ) : GridData where
  k := R.k
  m := R.m
  t := R.t
  s := s
  ga := ga
  v := extend 2 P.v
  b := extend 1 P.b
  e := extend 1 P.e
  cen := cen
  two_le_k := by have := R.m_add_three_le_k; omega
  v_anti := by
    intro i j hi hij hj
    have hs : ∀ (a : ℕ) (h : a + 1 < R.k - 1), P.v ⟨a + 1, h⟩ < P.v ⟨a, by omega⟩ :=
      fun a h => (P.u_gt_v ⟨a + 1, h⟩).trans (P.v_gt_u ⟨a, by omega⟩)
    have hA : ∀ (d a : ℕ) (h : a + d + 1 < R.k - 1), P.v ⟨a + d + 1, h⟩ < P.v ⟨a, by omega⟩ := by
      intro d
      induction d with
      | zero => exact hs
      | succ d ih => intro a h; exact (hs (a + d + 1) h).trans (ih a (by omega))
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' hi
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
    have h := hA d a (by omega)
    rw [← extend_cast 2 P.v_int, ← extend_cast 2 P.v_int] at h
    rw [show a + 2 + d + 1 = a + d + 1 + 2 by omega]
    exact_mod_cast h
  b_mono := by
    intro i j hi hij hj
    have hs : ∀ (a : ℕ) (h : a + 1 < R.m), P.b ⟨a, by omega⟩ < P.b ⟨a + 1, h⟩ := fun a h => by
      have h1 := P.gap_be ⟨a, by omega⟩
      have h2 := P.gap_eb ⟨a, by omega⟩ h
      have h3 : (0 : ℚ) ≤ R.t := by positivity
      linarith
    have hA : ∀ (d a : ℕ) (h : a + d + 1 < R.m), P.b ⟨a, by omega⟩ < P.b ⟨a + d + 1, h⟩ := by
      intro d
      induction d with
      | zero => exact hs
      | succ d ih => intro a h; exact (ih a (by omega)).trans (hs (a + d + 1) h)
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' hi
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
    have h := hA d a (by omega)
    rw [← extend_cast 1 P.b_int, ← extend_cast 1 P.b_int] at h
    rw [show a + 1 + d + 1 = a + d + 1 + 1 by omega]
    exact_mod_cast h

theorem ofHCParam_spec {R : Ranks} (P : HCParam R) (s ga : ℕ) (cen : ℕ → ℤ) :
    (∀ i, P.v i = (ofHCParam P s ga cen).v (i.1 + 2)) ∧ (∀ l, P.b l = (ofHCParam P s ga cen).b (l.1 + 1)) ∧
      ∀ l, P.e l = (ofHCParam P s ga cen).e (l.1 + 1) :=
  ⟨fun i => (extend_cast 2 P.v_int i).symm, fun l => (extend_cast 1 P.b_int l).symm,
    fun l => (extend_cast 1 P.e_int l).symm⟩

end GridData

def exGrid : GridData where
  k := 4
  m := 2
  t := 3
  s := 3
  ga := 8
  v := fun i => 4 - i
  b := fun l => 6 * l - 5
  e := fun j => 6 * j - 2
  cen := fun i => 30 - 8 * i
  two_le_k := by norm_num
  v_anti := by intro i j _ _ _; omega
  b_mono := by intro i j _ _ _; omega

theorem exGrid_lam : exGrid.lam =
    {(53 / 2, true), (37 / 2, false), (21 / 2, true), (3 / 2, true), (1 / 2, true), (-1 / 2, true)} := by decide +kernel

theorem example_discrete_parameter : exGrid.parD0 = {(2, true), (1, true), (0, true), (-1, true), (-7, false)} := by decide +kernel

theorem exGrid_parD : exGrid.parD 1 1 =
    plus {15, 14, 13, 2, 1, 0, -1, -3, -4, -5, -7} := by decide +kernel

theorem exGrid_parPi : exGrid.parPi 1 = {(53 / 2, false), (37 / 2, true), (29 / 2, true), (27 / 2, true), (21 / 2, true),
    (3 / 2, true), (1 / 2, true), (-1 / 2, true)} := by decide +kernel

theorem exGrid_signature : signature exGrid.lam = (5, 1) ∧ signature exGrid.parD0 = (4, 1) ∧
    ncGap exGrid.lam = ((8 : ℚ) : WithTop ℚ) ∧ ncGap exGrid.parD0 = ((6 : ℚ) : WithTop ℚ) ∧ exGrid.NearMid := by
  decide +kernel

theorem exGrid_word : word exGrid.lam exGrid.parD0 =
    [.plus, .minus, .plus, .circPlus, .plus, .circPlus, .plus, .circPlus, .plus, .circPlus, .circMinus] := by
  rw [word_eq (L := [53 / 2, 37 / 2, 21 / 2, 2, 3 / 2, 1, 1 / 2, 0, -1 / 2, -1, -7]) (by decide +kernel)
    (by decide +kernel)]
  decide +kernel

theorem exGrid_interlace : HeInterlace exGrid.lam exGrid.parD0 ∧
    StrictInterlace (exGrid.weightX 2) (entries (exGrid.parD 2 2)) ∧
    ¬ StrictInterlace (exGrid.weightX 1) (entries (exGrid.parD 2 2)) := by decide +kernel

theorem exGrid_lift : exGrid.parD 1 0 = liftMinus 14 3 (exGrid.parD 0 0) ∧
    exGrid.parD 0 1 = liftPlus (-4) 3 (exGrid.parD 0 0) ∧ exGrid.parPi 1 = liftMinus 14 2 (exGrid.parPi 0) ∧
    exGrid.parD 1 0 ≠ liftPlus 14 3 (exGrid.parD 0 0) ∧ exGrid.parD 0 1 ≠ liftMinus (-4) 3 (exGrid.parD 0 0) := by
  decide +kernel

example : HeInterlace {(5, true), (3, false), (1, false)} {(5 / 2, false), (1 / 2, false)} ∧
    ¬ HeInterlace {(5, true), (3, false), (1, false)} {(5 / 2, false), (3 / 2, false)} := by decide +kernel

example : highestWeight (n := 2) {5 / 2, -1 / 2} (by decide +kernel) = ![2, 0] := by
  have h : descEnum (n := 2) {5 / 2, -1 / 2} (by decide +kernel) = ![5 / 2, -1 / 2] :=
    descEnum_unique _ (by decide +kernel) (by decide +kernel)
  funext i
  simp only [highestWeight, h]
  fin_cases i <;> norm_num

end GlobalTheory.SignedHC
