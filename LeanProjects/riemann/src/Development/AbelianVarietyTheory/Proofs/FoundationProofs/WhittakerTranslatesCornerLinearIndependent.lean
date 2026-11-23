import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial

noncomputable section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare.Indep

lemma inv_of_mul_closed {G : Type} [Group G] [Finite G] (S : G → Prop) (h1 : S 1)
    (hm : ∀ a b, S a → S b → S (a * b)) (a : G) (ha : S a) : S a⁻¹ := by
  have hp : ∀ n : ℕ, S (a ^ n) := by
    intro n
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ]; exact hm _ _ ih ha
  have hpos : 0 < orderOf a := orderOf_pos a
  have : a⁻¹ = a ^ (orderOf a - 1) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  rw [this]; exact hp _

variable {g : ℕ} [Fact g.Prime] {N : ℕ}

def RowUp (k : ℕ) (h : GG g N) : Prop :=
  ∀ a : Fin N, k ≤ (a : ℕ) → h.val a a = 1 ∧ ∀ b, b < a → h.val a b = 0

def Corner (k : ℕ) (h : GG g N) : Prop :=
  ∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → h.val a b = if a = b then 1 else 0

lemma rowUp_one (k : ℕ) : RowUp k (1 : GG g N) := by
  intro a _
  refine ⟨by simp, fun b hb => ?_⟩
  simp [Matrix.one_apply, hb.ne']

lemma rowUp_mul (k : ℕ) (h h' : GG g N) (H : RowUp k h) (H' : RowUp k h') : RowUp k (h * h') := by
  have key : ∀ a b : Fin N, k ≤ (a : ℕ) → b ≤ a → (h * h').val a b = h'.val a b := by
    intro a b ha hb
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [(H a ha).1, one_mul]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with hc | hc
      · rw [(H a ha).2 c hc, zero_mul]
      · rw [(H' c (le_trans ha (le_of_lt hc))).2 b (lt_of_le_of_lt hb hc), mul_zero]
    · simp
  intro a ha
  refine ⟨by rw [key a a ha le_rfl, (H' a ha).1], fun b hb => ?_⟩
  rw [key a b ha hb.le, (H' a ha).2 b hb]

lemma rowUp_inv (k : ℕ) (h : GG g N) (H : RowUp k h) : RowUp k h⁻¹ :=
  inv_of_mul_closed (RowUp k) (rowUp_one k) (rowUp_mul k) h H

lemma corner_one (k : ℕ) : Corner k (1 : GG g N) := by
  intro a b _
  simp [Matrix.one_apply]

lemma corner_mul (k : ℕ) (h h' : GG g N) (H : Corner k h) (H' : Corner k h') : Corner k (h * h') := by
  intro a b hab
  rw [Units.val_mul, Matrix.mul_apply]
  rcases hab with ha | hb
  · rw [Finset.sum_eq_single a]
    · rw [H a a (Or.inl ha), H' a b (Or.inl ha)]; simp
    · intro c _ hc
      rw [H a c (Or.inl ha)]; simp [hc.symm]
    · simp
  · rw [Finset.sum_eq_single b]
    · rw [H a b (Or.inr hb), H' b b (Or.inr hb)]; simp
    · intro c _ hc
      rw [H' c b (Or.inr hb)]; simp [hc]
    · simp

lemma corner_inv (k : ℕ) (h : GG g N) (H : Corner k h) : Corner k h⁻¹ :=
  inv_of_mul_closed (Corner k) (corner_one k) (corner_mul k) h H

lemma Corner.rowUp {k : ℕ} {h : GG g N} (H : Corner k h) : RowUp k h := by
  intro a ha
  refine ⟨by rw [H a a (Or.inl ha)]; simp, fun b hb => ?_⟩
  rw [H a b (Or.inl ha)]; simp [hb.ne']

lemma rowUp_zero_iff (h : GG g N) : RowUp 0 h ↔ IsUp g N h :=
  ⟨fun H => ⟨fun a => (H a (Nat.zero_le _)).1, fun a b hb => (H a (Nat.zero_le _)).2 b hb⟩,
    fun H a _ => ⟨H.1 a, fun b hb => H.2 a b hb⟩⟩

def colElt (n : Fin N) (w : Fin N → ZMod g) (hw : w n = 0) : GG g N where
  val := 1 + Matrix.vecMulVec w (Pi.single n 1)
  inv := 1 - Matrix.vecMulVec w (Pi.single n 1)
  val_inv := by
    have : Matrix.vecMulVec w (Pi.single n (1 : ZMod g)) * Matrix.vecMulVec w (Pi.single n (1 : ZMod g)) = 0 := by
      rw [Matrix.vecMulVec_mul_vecMulVec]; simp [hw]
    rw [add_mul, mul_sub, mul_sub, this]; simp
  inv_val := by
    have : Matrix.vecMulVec w (Pi.single n (1 : ZMod g)) * Matrix.vecMulVec w (Pi.single n (1 : ZMod g)) = 0 := by
      rw [Matrix.vecMulVec_mul_vecMulVec]; simp [hw]
    rw [sub_mul, mul_add, mul_add, this]; simp

lemma conj_colElt (n : Fin N) (w : Fin N → ZMod g) (hw : w n = 0) (h : GG g N) (a b : Fin N) :
    (h⁻¹ * colElt n w hw * h).val a b =
      (if a = b then 1 else 0) + (∑ c, (h⁻¹).val a c * w c) * h.val n b := by
  have e : (h⁻¹ * colElt n w hw * h).val =
      1 + (h⁻¹).val * Matrix.vecMulVec w (Pi.single n 1) * h.val := by
    rw [Units.val_mul, Units.val_mul]
    show (h⁻¹).val * (1 + Matrix.vecMulVec w (Pi.single n 1)) * h.val = _
    rw [mul_add, add_mul, mul_one, Units.inv_mul]
  rw [e, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply]
  simp [Matrix.mulVec, dotProduct]

lemma act_colElt {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ (GG g N) M) (L : Lev g N)
    (hL : L.sharp = false) (x : M) (hx : ∀ u, IsUp g N u → ρ u x = L.chi u • x) (m n : Fin N) (hmn : (n : ℕ) = m + 1)
    (w : Fin N → ZMod g) (hw : ∀ c, n ≤ c → w c = 0) (h : GG g N) (H : RowUp n h) :
    ρ (colElt n w (hw n le_rfl)) (ρ h x) = L.ψ ((L.co m : ZMod g) * ∑ c, (h⁻¹).val m c * w c) • ρ h x := by
  have Hi := rowUp_inv _ _ H
  have hz : ∀ a : Fin N, n ≤ a → ∑ c, (h⁻¹).val a c * w c = 0 := by
    intro a ha
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c n with hc | hc
    · rw [(Hi a ha).2 c (lt_of_lt_of_le hc ha), zero_mul]
    · rw [hw c hc, mul_zero]
  have hn := H n le_rfl
  have hle : ∀ a b : Fin N, b ≤ a → (∑ c, (h⁻¹).val a c * w c) * h.val n b = 0 := by
    intro a b hb
    rcases lt_or_ge a n with hc | hc
    · rw [hn.2 b (lt_of_le_of_lt hb hc), mul_zero]
    · rw [hz a hc, zero_mul]
  set u := h⁻¹ * colElt n w (hw n le_rfl) * h with hu
  have hup : IsUp g N u := by
    refine ⟨fun a => ?_, fun a b hb => ?_⟩
    · rw [hu, conj_colElt, hle a a le_rfl]; simp
    · rw [hu, conj_colElt, hle a b hb.le]; simp [hb.ne']
  have hchi : L.chi u = L.ψ ((L.co m : ZMod g) * ∑ c, (h⁻¹).val m c * w c) := by
    unfold Lev.chi
    congr 1
    have hE : ∀ a b : Fin N, L.Edge a b ↔ (b : ℕ) = a + 1 := by
      intro a b; simp [Lev.Edge, hL]
    rw [Finset.sum_eq_single m, Finset.sum_eq_single n]
    · rw [if_pos ((hE m n).2 hmn), hu, conj_colElt, hn.1, if_neg (by intro e; rw [e] at hmn; omega)]
      simp
    · intro b _ hb
      rw [if_neg]
      intro e
      exact hb (Fin.ext (by rw [(hE m b).1 e, hmn]))
    · simp
    · intro a _ ha
      refine Finset.sum_eq_zero fun b _ => ?_
      split_ifs with e
      · have e' := (hE a b).1 e
        rw [hu, conj_colElt, if_neg (by intro e; rw [e] at e'; omega), zero_add]
        have ha' : (a : ℕ) ≠ m := fun e => ha (Fin.ext e)
        rcases lt_or_ge a n with hc | hc
        · rw [hn.2 b (by rw [Fin.lt_def] at hc ⊢; omega)]; simp
        · rw [hz a hc]; simp
      · rfl
    · simp
  have e : colElt n w (hw n le_rfl) * h = h * u := by rw [hu]; group
  rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hx u hup, map_smul, hchi]

lemma sum_char (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (d : Fin N → ZMod g) (hd : d ≠ 0) :
    ∑ v : Fin N → ZMod g, ψ (∑ c, d c * v c) = 0 := by
  obtain ⟨c, hc⟩ := Function.ne_iff.1 hd
  obtain ⟨t, ht⟩ := DFunLike.ne_iff.1 hψ
  have hc' : d c ≠ 0 := hc
  have ht' : ψ t ≠ 1 := by simpa using ht
  have e := Equiv.sum_comp (Equiv.addRight (Pi.single c (t / d c) : Fin N → ZMod g))
    (fun v : Fin N → ZMod g => ψ (∑ c, d c * v c))
  have e2 : ∀ v : Fin N → ZMod g, ψ (∑ c', d c' * (Equiv.addRight (Pi.single c (t / d c) : Fin N → ZMod g) v) c') =
      ψ t * ψ (∑ c, d c * v c) := by
    intro v
    rw [← AddChar.map_add_eq_mul]
    congr 1
    simp only [Equiv.coe_addRight, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    rw [Finset.sum_eq_single c]
    · simp; field_simp
    · intro b _ hb; simp [hb]
    · simp
  simp only [e2, ← Finset.mul_sum] at e
  have : (ψ t - 1) * ∑ v : Fin N → ZMod g, ψ (∑ c, d c * v c) = 0 := by rw [sub_mul, e]; simp
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 ht')

lemma step {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ (GG g N) M) (L : Lev g N)
    (hL : L.sharp = false) (x : M) (hx : ∀ u, IsUp g N u → ρ u x = L.chi u • x) (k : ℕ) (hk : k + 1 < N)
    (φ : GG g N → ℂ) (hφ : ∀ h, φ h ≠ 0 → RowUp (k + 1) h) (hs : ∑ h, φ h • ρ h x = 0) :
    ∑ h, (if RowUp k h then φ h else 0) • ρ h x = 0 := by
  let m : Fin N := ⟨k, by omega⟩
  let n : Fin N := ⟨k + 1, hk⟩
  let tr : (Fin N → ZMod g) → Fin N → ZMod g := fun v c => if c < n then v c else 0
  have htr : ∀ v c, n ≤ c → tr v c = 0 := fun v c hc => if_neg (not_lt.2 hc)
  let d : GG g N → Fin N → ZMod g := fun h c =>
    if c < n then (L.co m : ZMod g) * ((h⁻¹).val m c - if m = c then 1 else 0) else 0
  have hmn : m < n := by simp [m, n, Fin.lt_def]
  have h1 : ∀ (v : Fin N → ZMod g) (h : GG g N),
      L.ψ (-((L.co m : ZMod g) * v m)) • ρ (colElt n (tr v) (htr v n le_rfl)) (φ h • ρ h x) =
        L.ψ (∑ c, d h c * v c) • φ h • ρ h x := by
    intro v h
    by_cases h0 : φ h = 0
    · simp [h0]
    rw [map_smul, act_colElt ρ L hL x hx m n rfl (tr v) (htr v) h (hφ h h0), smul_comm (φ h), smul_smul,
      ← AddChar.map_add_eq_mul]
    congr 2
    have : v m = ∑ c, (if m = c then 1 else 0) * tr v c := by
      rw [Finset.sum_eq_single m]
      · simp [tr, hmn]
      · intro b _ hb; simp [hb.symm]
      · simp
    rw [this, neg_add_eq_sub, ← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [d, tr]
    split_ifs <;> ring
  have h2 : ∀ h : GG g N, (∑ v : Fin N → ZMod g, L.ψ (∑ c, d h c * v c)) • φ h • ρ h x =
      (Fintype.card (Fin N → ZMod g) : ℂ) • (if RowUp k h then φ h else 0) • ρ h x := by
    intro h
    by_cases h0 : φ h = 0
    · simp [h0]
    by_cases hR : RowUp k h
    · have Hi := rowUp_inv _ _ hR m le_rfl
      have : d h = 0 := by
        funext c
        simp only [d]
        split_ifs with a b
        · subst b; rw [Hi.1]; simp
        · rw [Hi.2 c (by
            have : (m : ℕ) ≠ c := fun e => b (Fin.ext e)
            simp only [Fin.lt_def, m, n] at a this ⊢; omega)]
          simp
        · rfl
      simp [this, hR]
    · rw [if_neg hR, sum_char L.ψ L.hψ]
      · simp
      · intro hd
        apply hR
        have Hi := rowUp_inv _ _ (hφ h h0)
        have hrow : ∀ c, c < n → (h⁻¹).val m c = if m = c then 1 else 0 := by
          intro c hc
          have := congrFun hd c
          simp only [d, if_pos hc, Pi.zero_apply] at this
          exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (L.co m).ne_zero)
        have : RowUp k h⁻¹ := by
          intro a ha
          rcases ha.eq_or_lt with e | e
          · have : a = m := Fin.ext e.symm
            subst this
            refine ⟨by rw [hrow _ hmn]; simp, fun b hb => ?_⟩
            rw [hrow _ (hb.trans hmn)]; simp [hb.ne']
          · exact Hi a e
        simpa using rowUp_inv _ _ this
  have h3 : ∑ v : Fin N → ZMod g,
      L.ψ (-((L.co m : ZMod g) * v m)) • ρ (colElt n (tr v) (htr v n le_rfl)) (∑ h, φ h • ρ h x) = 0 := by
    simp [hs]
  simp only [map_sum, Finset.smul_sum] at h3
  rw [Finset.sum_comm, Finset.sum_congr rfl fun h _ => ((Finset.sum_congr rfl fun v _ => h1 v h).trans (Finset.sum_smul.symm.trans (h2 h))), ← Finset.smul_sum] at h3
  exact (smul_eq_zero.1 h3).resolve_left (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

lemma sum_up {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ (GG g N) M) (L : Lev g N)
    (hL : L.sharp = false) (x : M) (hx0 : x ≠ 0) (hx : ∀ u, IsUp g N u → ρ u x = L.chi u • x) (k : ℕ) (hk : k < N)
    (φ : GG g N → ℂ) (hφ : ∀ h, φ h ≠ 0 → RowUp k h) (hs : ∑ h, φ h • ρ h x = 0) :
    ∑ u, (if IsUp g N u then φ u * L.chi u else 0) = 0 := by
  induction k generalizing φ with
  | zero =>
    have : ∀ h, φ h • ρ h x = (if IsUp g N h then φ h * L.chi h else 0) • x := by
      intro h
      by_cases h0 : φ h = 0
      · simp [h0]
      have := (rowUp_zero_iff h).1 (hφ h h0)
      rw [if_pos this, hx h this, smul_smul]
    simp only [this, ← Finset.sum_smul] at hs
    exact (smul_eq_zero.1 hs).resolve_right hx0
  | succ k ih =>
    have := ih (by omega) (fun h => if RowUp k h then φ h else 0)
      (fun h hh => by by_contra e; exact hh (if_neg e)) (step ρ L hL x hx k hk φ hφ hs)
    refine Eq.trans (Finset.sum_congr rfl fun u _ => ?_) this
    split_ifs with a b
    · rfl
    · exact absurd (fun c _ => ⟨a.1 c, fun b hb => a.2 c b hb⟩) b
    · rfl

theorem translates_independent : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M), ∀ (L : Lev g N), L.sharp = false → ∀ (x : M), x ≠ 0 → (∀ u, IsUp g N u → ρ u x = L.chi u • x) → ∀ k : ℕ, k < N → ∀ φ : GG g N → ℂ, (∀ h, φ h ≠ 0 → (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (h : GG g N).val a b = if a = b then 1 else 0)) → ∑ h, φ h • ρ h x = 0 → ∀ h₀ : GG g N, ∑ u ∈ Finset.univ.filter (fun u : GG g N => IsUp g N u ∧ (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (u : GG g N).val a b = if a = b then 1 else 0)), φ (h₀ * u) * L.chi u = 0 := by
  intro g _ N M _ _ _ ρ L hL x hx0 hx k hk φ hφ hs h₀
  have hφ' : ∀ h, φ h ≠ 0 → Corner k h := hφ
  by_cases h0 : Corner k h₀
  · have hc : ∀ p, φ (h₀ * p) ≠ 0 → Corner k p := by
      intro p hp
      simpa using corner_mul k _ _ (corner_inv k _ h0) (hφ' _ hp)
    have hs' : ∑ p, φ (h₀ * p) • ρ p x = 0 := by
      have e := Equiv.sum_comp (Equiv.mulLeft h₀) (fun h => φ h • ρ h x)
      have e2 := congrArg (ρ h₀⁻¹) (e.trans hs)
      rw [map_sum, map_zero] at e2
      rw [← e2]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [Equiv.coe_mulLeft, map_smul]
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_left]
    have := sum_up ρ L hL x hx0 hx k hk (fun p => φ (h₀ * p)) (fun p hp => (hc p hp).rowUp) hs'
    rw [Finset.sum_filter]
    refine Eq.trans (Finset.sum_congr rfl fun u _ => ?_) this
    by_cases e : φ (h₀ * u) = 0
    · simp [e]
    have hu : ∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → u.val a b = if a = b then 1 else 0 := hc u e
    by_cases e' : IsUp g N u
    · rw [if_pos ⟨e', hu⟩, if_pos e']
    · rw [if_neg (fun h => e' h.1), if_neg e']
  · refine Finset.sum_eq_zero fun u hu => ?_
    have hu' : Corner k u := (Finset.mem_filter.1 hu).2.2
    have : φ (h₀ * u) = 0 := by
      by_contra e
      apply h0
      simpa using corner_mul k _ _ (hφ' _ e) (corner_inv k _ hu')
    rw [this, zero_mul]

end GlobalTheory.BadShare.Indep
