import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial

noncomputable section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare.Cells

section Comb
variable {F : Type} [Field F]

def Good (k : ℕ) (d : ℕ → F) : Prop := d 0 ≠ 0 ∧ ∀ a, k ≤ a → d a = 1

def st (d : ℕ → F) (b : ℕ) : ℕ := Nat.findGreatest (fun a => d a ≠ 0) b

def en (d : ℕ → F) (b : ℕ) : ℕ := sInf {a | b < a ∧ d a ≠ 0}

def sg (k : ℕ) (d : ℕ → F) (b : ℕ) : ℕ := if b < k then k - en d b + (b - st d b) else b

lemma st_le (d : ℕ → F) (b : ℕ) : st d b ≤ b := Nat.findGreatest_le b

lemma st_ne {k : ℕ} {d : ℕ → F} (h : Good k d) (b : ℕ) : d (st d b) ≠ 0 :=
  Nat.findGreatest_spec (P := fun a => d a ≠ 0) (Nat.zero_le b) h.1

lemma le_st {d : ℕ → F} {a b : ℕ} (hab : a ≤ b) (ha : d a ≠ 0) : a ≤ st d b :=
  Nat.le_findGreatest (P := fun a => d a ≠ 0) hab ha

lemma en_spec {k : ℕ} {d : ℕ → F} (h : Good k d) (b : ℕ) : b < en d b ∧ d (en d b) ≠ 0 := by
  have : ({a | b < a ∧ d a ≠ 0} : Set ℕ).Nonempty :=
    ⟨b + k + 1, by omega, by rw [h.2 _ (by omega)]; exact one_ne_zero⟩
  exact Nat.sInf_mem this

lemma en_le {d : ℕ → F} {a b : ℕ} (hab : b < a) (ha : d a ≠ 0) : en d b ≤ a :=
  Nat.sInf_le (show a ∈ {a | b < a ∧ d a ≠ 0} from ⟨hab, ha⟩)

lemma en_le_k {k : ℕ} {d : ℕ → F} (h : Good k d) {b : ℕ} (hb : b < k) : en d b ≤ k :=
  en_le hb (by rw [h.2 _ le_rfl]; exact one_ne_zero)

lemma dich {k : ℕ} {d : ℕ → F} (h : Good k d) {c b : ℕ} (hcb : c < b) :
    (st d c = st d b ∧ en d c = en d b) ∨ en d c ≤ st d b := by
  by_cases h1 : en d c ≤ b
  · exact Or.inr (le_st h1 (en_spec h c).2)
  · left
    have h2 := en_le (d := d) (b := c) (a := en d b) (by have := (en_spec h b).1; omega) (en_spec h b).2
    have h3 := en_le (d := d) (b := b) (a := en d c) (by omega) (en_spec h c).2
    have h4 := le_st (d := d) (a := st d c) (b := b) (by have := st_le d c; omega) (st_ne h c)
    refine ⟨?_, by omega⟩
    by_cases h5 : st d b ≤ c
    · have := le_st h5 (st_ne h b); omega
    · have := en_le (d := d) (b := c) (a := st d b) (by omega) (st_ne h b)
      have := st_le d b; omega

lemma sg_lt {k : ℕ} {d : ℕ → F} (h : Good k d) {b : ℕ} (hb : b < k) : sg k d b < k := by
  have := en_spec h b; have := en_le_k h hb; have := st_le d b
  simp only [sg, if_pos hb]; omega

lemma sg_ge {k : ℕ} (d : ℕ → F) {b : ℕ} (hb : k ≤ b) : sg k d b = b := by
  simp only [sg, if_neg (not_lt.2 hb)]

lemma sg_dich {k : ℕ} {d : ℕ → F} (h : Good k d) {c b : ℕ} (hcb : c < b) (hb : b < k) :
    (st d c = st d b ∧ sg k d c + b = sg k d b + c) ∨ (c < st d b ∧ sg k d b < sg k d c) := by
  have hc : c < k := by omega
  have := en_spec h b; have := en_le_k h hb; have := st_le d b
  have := en_spec h c; have := en_le_k h hc; have := st_le d c
  simp only [sg, if_pos hb, if_pos hc]
  rcases dich h hcb with h1 | h1 <;> omega

lemma sg_inj {k : ℕ} {d : ℕ → F} (h : Good k d) : Function.Injective (sg k d) := by
  intro c b hcb
  wlog hlt : c < b generalizing c b
  · rcases Nat.lt_or_ge b c with h1 | h1
    · exact (this hcb.symm h1).symm
    · omega
  by_cases hb : b < k
  · have := sg_dich h hlt hb; omega
  · rw [sg_ge d (not_lt.1 hb)] at hcb
    by_cases hc : c < k
    · have := sg_lt h hc; omega
    · rwa [sg_ge d (not_lt.1 hc)] at hcb

lemma st_ge {k : ℕ} {d : ℕ → F} (h : Good k d) {b : ℕ} (hb : k ≤ b) : d (st d b) = 1 := by
  have := le_st (d := d) hb (by rw [h.2 _ le_rfl]; exact one_ne_zero)
  exact h.2 _ this

lemma st_eq_iff {k : ℕ} {d : ℕ → F} (h : Good k d) (b : ℕ) : st d b = b ↔ d b ≠ 0 := by
  constructor
  · intro h1; have := st_ne h b; rwa [h1] at this
  · intro h1; exact le_antisymm (st_le d b) (le_st le_rfl h1)

lemma ext_of {k : ℕ} {d d' : ℕ → F} (h : Good k d) (h' : Good k d')
    (H : ∀ b < k, sg k d b = sg k d' b ∧ d (st d b) = d' (st d' b)) : d = d' := by
  funext b
  by_cases hb : b < k
  swap
  · rw [h.2 b (not_lt.1 hb), h'.2 b (not_lt.1 hb)]
  have key : st d b = b ↔ st d' b = b := by
    have := st_le d b; have := st_le d' b
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · omega
    · have := sg_dich h (c := b - 1) (b := b) (by omega) hb
      have := sg_dich h' (c := b - 1) (b := b) (by omega) hb
      have := (H b hb).1
      have := (H (b - 1) (by omega)).1
      have := st_le d (b - 1); have := st_le d' (b - 1)
      omega
  by_cases h1 : st d b = b
  · have := (H b hb).2
    rwa [h1, key.1 h1] at this
  · have h2 : ¬ st d' b = b := fun h2 => h1 (key.2 h2)
    rw [st_eq_iff h, not_not] at h1
    rw [st_eq_iff h', not_not] at h2
    rw [h1, h2]

def mono {N : ℕ} (σ : Equiv.Perm (Fin N)) (t : Fin N → F) (ht : ∀ b, t b ≠ 0) : GL (Fin N) F where
  val := Matrix.of fun a b => if a = σ b then t b else 0
  inv := Matrix.of fun a b => if b = σ a then (t a)⁻¹ else 0
  val_inv := by
    ext a b
    obtain ⟨c, rfl⟩ := σ.surjective a
    rw [Matrix.mul_apply, Finset.sum_eq_single c]
    · by_cases h : σ c = b
      · subst h; simp [ht]
      · simp [h, Ne.symm h]
    · intro x _ hx; simp [Ne.symm hx]
    · simp
  inv_val := by
    ext a b
    rw [Matrix.mul_apply, Finset.sum_eq_single (σ a)]
    · by_cases h : a = b
      · subst h; simp [ht]
      · simp [h]
    · intro x _ hx; simp [hx]
    · simp

lemma mono_val {N : ℕ} (σ : Equiv.Perm (Fin N)) (t : Fin N → F) (ht : ∀ b, t b ≠ 0) (a b : Fin N) :
    (mono σ t ht).val a b = if a = σ b then t b else 0 := rfl

lemma mono_rel {N : ℕ} (σ : Equiv.Perm (Fin N)) (t : Fin N → F) (ht : ∀ b, t b ≠ 0) (u u' : GL (Fin N) F)
    (h : u * mono σ t ht = mono σ t ht * u') (c b : Fin N) : u.val (σ c) (σ b) * t b = t c * u'.val c b := by
  have := congrArg (fun x : GL (Fin N) F => x.val (σ c) b) h
  simpa [Units.val_mul, Matrix.mul_apply, mono_val] using this

def perm {k N : ℕ} (hk : k < N) {d : ℕ → F} (h : Good k d) : Equiv.Perm (Fin N) :=
  Equiv.ofBijective (fun b => ⟨sg k d b, by
      by_cases hb : (b : ℕ) < k
      · have := sg_lt h hb; omega
      · rw [sg_ge d (not_lt.1 hb)]; exact b.2⟩)
    (Finite.injective_iff_bijective.1 fun a b hab => Fin.ext (sg_inj h (congrArg Fin.val hab)))

lemma perm_val {k N : ℕ} (hk : k < N) {d : ℕ → F} (h : Good k d) (b : Fin N) : (perm hk h b : ℕ) = sg k d b := rfl

def cell {k N : ℕ} (hk : k < N) {d : ℕ → F} (h : Good k d) : GL (Fin N) F :=
  mono (perm hk h) (fun b => d (st d b)) fun b => st_ne h b

def dat (k : ℕ) (p : Fˣ × (Fin (k - 1) → F)) (a : ℕ) : F :=
  if k ≤ a then 1 else if a = 0 then (p.1 : F) else if h : a - 1 < k - 1 then p.2 ⟨a - 1, h⟩ else 1

lemma dat_good (k : ℕ) (p : Fˣ × (Fin (k - 1) → F)) : Good k (dat k p) := by
  refine ⟨?_, fun a ha => by simp [dat, ha]⟩
  unfold dat
  split_ifs <;> simp_all

lemma dat_inj {k : ℕ} (hk : 0 < k) : Function.Injective (dat (F := F) k) := by
  intro p q h
  ext i
  · have := congrFun h 0
    simpa [dat, hk.ne'] using this
  · have := congrFun h (i + 1)
    have hi := i.2
    have h1 : ¬ k ≤ i + 1 := by omega
    simpa [dat, h1] using this

lemma cell_inj {k N : ℕ} (hk : k < N) {d d' : ℕ → F} (h : Good k d) (h' : Good k d') (H : cell hk h = cell hk h') :
    d = d' := by
  refine ext_of h h' fun b hb => ?_
  have h1 := congrArg (fun x : GL (Fin N) F => x.val (perm hk h ⟨b, by omega⟩) ⟨b, by omega⟩) H
  simp only [cell, mono_val, if_true] at h1
  split_ifs at h1 with h2
  · exact ⟨congrArg Fin.val h2, h1⟩
  · exact absurd h1 (st_ne h b)

end Comb

theorem relevant_cells : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (L : Lev g N), L.sharp = false → (∀ a, L.co a = 1) → ∀ k : ℕ, 0 < k → k < N → ∃ R : Finset (GG g N), (g - 1) * g ^ (k - 1) ≤ R.card ∧ (∀ w ∈ R, (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (w : GG g N).val a b = if a = b then 1 else 0) ∧ ∃ σ : Equiv.Perm (Fin N), ∀ a b, w.val a b ≠ 0 → a = σ b) ∧ ∀ w ∈ R, ∀ u u' : GG g N, IsUp g N u → IsUp g N u' → (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (u : GG g N).val a b = if a = b then 1 else 0) → (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (u' : GG g N).val a b = if a = b then 1 else 0) → u * w = w * u' → L.chi u = L.chi u' := by
  intro g _ N L hs hco k hk0 hk
  refine ⟨Finset.univ.image fun p : (ZMod g)ˣ × (Fin (k - 1) → ZMod g) => cell hk (dat_good k p), ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ fun p q h => dat_inj hk0 (cell_inj hk _ _ h)]
    simp [Nat.totient_prime (Fact.out : g.Prime)]
  · intro w hw
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hw
    have h := dat_good k p
    refine ⟨fun a b hab => ?_, perm hk h, fun a b hab => ?_⟩
    · simp only [cell, mono_val, Fin.ext_iff, perm_val]
      by_cases hb : (b : ℕ) < k
      · have := sg_lt h hb
        rw [if_neg (by omega), if_neg (by omega)]
      · rw [sg_ge _ (not_lt.1 hb), st_ge h (not_lt.1 hb)]
    · by_contra h1
      exact hab (by simp only [cell, mono_val]; exact if_neg h1)
  · intro w hw u u' hu hu' hb hb' H
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hw
    have h := dat_good k p
    set d := dat k p
    have rel := mono_rel _ _ _ u u' H
    unfold Lev.chi
    congr 1
    rw [← Equiv.sum_comp (perm hk h)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Equiv.sum_comp (perm hk h)]
    refine Finset.sum_congr rfl fun b _ => ?_
    have r := rel c b
    simp only [Lev.Edge, hs, hco, Units.val_one, one_mul, Bool.false_eq_true, if_false, perm_val]
    have tb := st_ne h b
    have tc := st_ne h c
    have hσ : ∀ x : Fin N, (x : ℕ) < k → sg k d x < k := fun x hx => sg_lt h hx
    have hσ' : ∀ x : Fin N, k ≤ (x : ℕ) → sg k d x = x := fun x hx => sg_ge d hx
    have z : c ≠ b → (k ≤ (b : ℕ) ∨ b < c ∨ sg k d b < sg k d c) →
        u.val (perm hk h c) (perm hk h b) = 0 ∧ u'.val c b = 0 := by
      intro hne hh
      have e1 : u'.val c b = 0 → u.val (perm hk h c) (perm hk h b) = 0 ∧ u'.val c b = 0 := fun e =>
        ⟨by rw [e, mul_zero] at r; exact (mul_eq_zero.1 r).resolve_right tb, e⟩
      rcases hh with hh | hh | hh
      · exact e1 (by rw [hb' c b (Or.inr hh), if_neg hne])
      · exact e1 (hu'.2 _ _ hh)
      · have e : u.val (perm hk h c) (perm hk h b) = 0 := hu.2 _ _ hh
        exact ⟨e, by rw [e, zero_mul] at r; exact (mul_eq_zero.1 r.symm).resolve_left tc⟩
    by_cases hne : c = b
    · subst hne; simp
    by_cases hh : k ≤ (b : ℕ) ∨ b < c ∨ sg k d b < sg k d c
    · obtain ⟨z1, z2⟩ := z hne hh
      simp [z1, z2]
    · have hne' : (c : ℕ) ≠ b := fun e => hne (Fin.ext e)
      simp only [not_or, Fin.lt_def] at hh
      rcases sg_dich h (c := c) (b := b) (by omega) (by omega) with ⟨e1, e2⟩ | e
      · have e3 : u.val (perm hk h c) (perm hk h b) = u'.val c b := by
          rw [e1, mul_comm] at r
          exact mul_left_cancel₀ tb r
        rw [e3]
        exact if_congr (by omega) rfl rfl
      · omega

end GlobalTheory.BadShare.Cells
