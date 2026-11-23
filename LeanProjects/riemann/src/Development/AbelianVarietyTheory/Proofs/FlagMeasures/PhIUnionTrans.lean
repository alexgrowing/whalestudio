import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PatternGroupSubgroupOrderCharacterStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotypicTraceEqOfOneDoubleCosetStatement

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

noncomputable section

namespace GlobalTheory.RootExch

variable {g : ℕ} [Fact g.Prime] {N : ℕ}

theorem pat_ne {Φ : Fin N → Fin N → Prop} {M : Mt g N} (hM : InPat Φ M) {a b : Fin N} (h : M a b ≠ 0) :
    a = b ∨ Φ a b := by
  by_contra hc
  push Not at hc
  exact h (by rw [hM a b hc.2, Matrix.one_apply_ne hc.1])

theorem conj_entry (A B : Mt g N) (u v : Fin N) (t : ZMod g) (x y : Fin N) :
    (A * Matrix.single u v t * B) x y = A x u * t * B v y := by
  rw [Matrix.mul_apply, Finset.sum_eq_single v]
  · simp
  · intro j _ hj
    simp [hj]
  · intro hv
    exact absurd (Finset.mem_univ v) hv

theorem sumAt_one {E : Fin N → Fin N → Prop} (hE : ∀ a, ¬ E a a) : sumAt E (1 : Mt g N) = 0 := by
  unfold sumAt
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  split_ifs with h
  · exact Matrix.one_apply_ne fun hab => by subst hab; exact hE a h
  · rfl

private theorem sumAt_one_add {E : Fin N → Fin N → Prop} (hE : ∀ a, ¬ E a a) (X : Mt g N) :
    sumAt E (1 + X) = sumAt E X := by
  unfold sumAt
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · rw [Matrix.add_apply, Matrix.one_apply_ne (fun hab => by subst hab; exact hE a h), zero_add]
  · rfl

theorem conj_pat {Φ Φ₁ E : Fin N → Fin N → Prop} (hE : ∀ a, ¬ E a a) {u v p q : Fin N} (hpq : E p q)
    (H : ∀ x y, (x = u ∨ Φ x u) → (v = y ∨ Φ v y) → Φ₁ x y ∧ (E x y → x = p ∧ y = q))
    {A B : Mt g N} (hA : InPat Φ A) (hB : InPat Φ B) (t : ZMod g) :
    InPat Φ₁ (1 + A * Matrix.single u v t * B) ∧
      sumAt E (1 + A * Matrix.single u v t * B) = A p u * t * B v q := by
  have hprod : ∀ x y, A x u ≠ 0 → B v y ≠ 0 → Φ₁ x y ∧ (E x y → x = p ∧ y = q) :=
    fun x y hx hy => H x y (pat_ne hA hx) (pat_ne hB hy)
  refine ⟨fun a b hab => ?_, ?_⟩
  · rw [Matrix.add_apply, conj_entry]
    by_cases hx : A a u = 0
    · simp [hx]
    by_cases hy : B v b = 0
    · simp [hy]
    exact absurd (hprod a b hx hy).1 hab
  · have h0 : ∀ a b, (a ≠ p ∨ b ≠ q) →
        (if E a b then (A * Matrix.single u v t * B) a b else 0) = 0 := by
      intro a b hab
      split_ifs with he
      · rw [conj_entry]
        by_contra hne
        have := (hprod a b (left_ne_zero_of_mul (left_ne_zero_of_mul hne))
          (right_ne_zero_of_mul hne)).2 he
        tauto
      · rfl
    rw [sumAt_one_add hE]
    unfold sumAt
    rw [Finset.sum_eq_single p (fun a _ ha => Finset.sum_eq_zero fun b _ => h0 a b (Or.inl ha)) (by simp),
      Finset.sum_eq_single q (fun b _ hb => h0 p b (Or.inr hb)) (by simp), if_pos hpq, conj_entry]

def patChar (ψ : AddChar (ZMod g) ℂ) (E : Fin N → Fin N → Prop) (hE : ∀ a, ¬ E a a) (H : Subgroup (Gn g N))
    (hm : ∀ x y : H, sumAt E (((x : Gn g N) : Mt g N) * ((y : Gn g N) : Mt g N)) =
      sumAt E ((x : Gn g N) : Mt g N) + sumAt E ((y : Gn g N) : Mt g N)) : H →* ℂˣ :=
  MonoidHom.toHomUnits
    { toFun := fun x => ψ (sumAt E ((x : Gn g N) : Mt g N))
      map_one' := by simp [sumAt_one hE]
      map_mul' := fun x y => by
        rw [← AddChar.map_add_eq_mul, ← hm]
        rfl }

theorem patChar_val (ψ : AddChar (ZMod g) ℂ) (E : Fin N → Fin N → Prop) (hE : ∀ a, ¬ E a a) (H : Subgroup (Gn g N))
    (hm) (x : H) : (patChar ψ E hE H hm x : ℂ) = ψ (sumAt E ((x : Gn g N) : Mt g N)) := rfl
set_option maxHeartbeats 1000000 in

theorem tr_ePat (ψ : AddChar (ZMod g) ℂ) (Φ E : Fin N → Fin N → Prop) (H : Subgroup (Gn g N))
    (hH : ∀ x, x ∈ H ↔ InPat Φ (x : Mt g N)) (χ : Gn g N → ℂ) :
    tr (ePat g N Φ E ψ) χ =
      (Nat.card H : ℂ)⁻¹ * ∑ a : H, (ψ (sumAt E ((a : Gn g N) : Mt g N)))⁻¹ * χ a := by
  have hS : ∀ x : Gn g N, x ∈ Finset.univ.filter (fun u : Gn g N => InPat Φ (u : Mt g N)) ↔ x ∈ H := by
    intro x
    simp [hH]
  have hc : ((Finset.univ.filter fun u : Gn g N => InPat Φ (u : Mt g N)).card : ℂ) = Nat.card H := by
    rw [← Nat.card_eq_finsetCard, Nat.card_congr (Equiv.subtypeEquivRight hS)]
  have hcoeff : ∀ x : Gn g N, (ePat g N Φ E ψ).coeff x =
      (Nat.card H : ℂ)⁻¹ * (if x ∈ H then (ψ (sumAt E (x : Mt g N)))⁻¹ else 0) := by
    intro x
    unfold ePat eDat
    simp only [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
      MonoidAlgebra.coeff_single, Finsupp.single_apply, Finset.sum_ite_eq', smul_eq_mul, hc]
    by_cases hx : x ∈ H
    · have hx' := (hH x).1 hx
      simp [hx, hx']
    · have hx' : ¬ InPat Φ (x : Mt g N) := fun h' => hx ((hH x).2 h')
      simp [hx, hx']
  have hsum : ∑ a : H, (ψ (sumAt E ((a : Gn g N) : Mt g N)))⁻¹ * χ a =
      ∑ x ∈ Finset.univ.filter (· ∈ H), (ψ (sumAt E (x : Mt g N)))⁻¹ * χ x :=
    (Finset.sum_subtype (p := (· ∈ H)) (Finset.univ.filter (· ∈ H)) (fun x => by simp)
      (fun x => (ψ (sumAt E (x : Mt g N)))⁻¹ * χ x)).symm
  unfold tr
  rw [hsum, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hcoeff]
  split_ifs <;> ring

theorem exists_conj (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) {Φ Φ₁ E : Fin N → Fin N → Prop}
    (hE : ∀ a, ¬ E a a) {u v p q : Fin N} (hpq : E p q)
    (H : ∀ x y, (x = u ∨ Φ x u) → (v = y ∨ Φ v y) → Φ₁ x y ∧ (E x y → x = p ∧ y = q))
    (hunit : ∀ M : Mt g N, InPat Φ₁ M → IsUnit M) (huv : p ≠ u ∨ v ≠ q)
    (H₁ : Subgroup (Gn g N)) (hH₁ : ∀ x, x ∈ H₁ ↔ InPat Φ₁ (x : Mt g N)) (hm)
    (h : Gn g N) (hA : InPat Φ ((h⁻¹ : Gn g N) : Mt g N)) (hB : InPat Φ (h : Mt g N))
    (hne : ((h⁻¹ : Gn g N) : Mt g N) p u * (h : Mt g N) v q ≠ 0) :
    ∃ a a' : H₁, (a' : Gn g N) = h⁻¹ * a * h ∧ patChar ψ E hE H₁ hm a' ≠ patChar ψ E hE H₁ hm a := by
  obtain ⟨s₀, hs₀⟩ := AddChar.ne_one_iff.1 hψ
  obtain ⟨t, ht⟩ : ∃ t : ZMod g, ((h⁻¹ : Gn g N) : Mt g N) p u * t * (h : Mt g N) v q = s₀ :=
    ⟨(((h⁻¹ : Gn g N) : Mt g N) p u * (h : Mt g N) v q)⁻¹ * s₀, by
      rw [show ∀ x y z w : ZMod g, x * (z * w) * y = x * y * z * w from fun x y z w => by ring,
        mul_inv_cancel₀ hne, one_mul]⟩
  have h1 : InPat Φ (1 : Mt g N) := fun a b _ => rfl
  obtain ⟨hM1, hM2⟩ := conj_pat hE hpq H h1 h1 t
  rw [one_mul, mul_one] at hM1 hM2
  have hzero : sumAt E (1 + Matrix.single u v t) = 0 := by
    rw [hM2]
    rcases huv with h' | h'
    · rw [Matrix.one_apply_ne h', zero_mul, zero_mul]
    · rw [Matrix.one_apply_ne h', mul_zero]
  obtain ⟨hA1, hA2⟩ := conj_pat hE hpq H hA hB t
  set a₀ : Gn g N := (hunit _ hM1).unit with ha₀def
  have ha₀ : (a₀ : Mt g N) = 1 + Matrix.single u v t := IsUnit.unit_spec _
  have hconj : ((h⁻¹ * a₀ * h : Gn g N) : Mt g N) =
      1 + ((h⁻¹ : Gn g N) : Mt g N) * Matrix.single u v t * (h : Mt g N) := by
    rw [Units.val_mul, Units.val_mul, ha₀, mul_add, add_mul, mul_one, Units.inv_mul]
  have hin : a₀ ∈ H₁ := (hH₁ _).2 (by rw [ha₀]; exact hM1)
  have hin' : h⁻¹ * a₀ * h ∈ H₁ := (hH₁ _).2 (by rw [hconj]; exact hA1)
  refine ⟨⟨a₀, hin⟩, ⟨h⁻¹ * a₀ * h, hin'⟩, rfl, fun heq => hs₀ ?_⟩
  have hv := congrArg (fun z : ℂˣ => (z : ℂ)) heq
  simp only [patChar_val] at hv
  change ψ (sumAt E ((h⁻¹ * a₀ * h : Gn g N) : Mt g N)) = ψ (sumAt E (a₀ : Mt g N)) at hv
  rw [hconj, hA2, ht, ha₀, hzero, AddChar.map_zero_eq_one] at hv
  exact hv

private theorem card_filter_fst_eq_and_snd (W : Fin N → Prop) (p : Fin N) :
    (Finset.univ.filter fun r : Fin N × Fin N => r.1 = p ∧ W r.2).card = (Finset.univ.filter W).card := by
  refine Finset.card_bij' (fun r _ => r.2) (fun w _ => (p, w)) ?_ ?_ ?_ ?_
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    exact hr.2
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact hw
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    exact Prod.ext hr.1.symm rfl
  · intro w _
    rfl

private theorem card_filter_fst_and_snd_eq (W : Fin N → Prop) (q : Fin N) :
    (Finset.univ.filter fun r : Fin N × Fin N => W r.1 ∧ r.2 = q).card = (Finset.univ.filter W).card := by
  refine Finset.card_bij' (fun r _ => r.1) (fun w _ => (w, q)) ?_ ?_ ?_ ?_
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    exact hr.1
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact ⟨hw, trivial⟩
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    exact Prod.ext rfl hr.2.symm
  · intro w _
    rfl

theorem exchange (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (Φ₁ Φ₂ E : Fin N → Fin N → Prop) (W : Fin N → Prop)
    (p q : Fin N) (hE : ∀ a, ¬ E a a) (hpq : E p q) (hp : ¬ W p) (hq : ¬ W q)
    (i1 : ∀ a, ¬ Φ₁ a a) (i2 : ∀ a, ¬ Φ₂ a a)
    (t1 : ∀ a b c, Φ₁ a b → Φ₁ b c → Φ₁ a c) (t2 : ∀ a b c, Φ₂ a b → Φ₂ b c → Φ₂ a c)
    (t0 : ∀ a b c, (Φ₁ a b ∨ Φ₂ a b) → (Φ₁ b c ∨ Φ₂ b c) → (Φ₁ a c ∨ Φ₂ a c))
    (e1 : ∀ a b c, Φ₁ a b → Φ₁ b c → ¬ E a c) (e2 : ∀ a b c, Φ₂ a b → Φ₂ b c → ¬ E a c)
    (d1 : ∀ a b, (Φ₁ a b ∧ ¬ Φ₂ a b) ↔ (a = p ∧ W b)) (d2 : ∀ a b, (Φ₂ a b ∧ ¬ Φ₁ a b) ↔ (W a ∧ b = q))
    (c1 : ∀ w, W w → ∀ x y, (x = p ∨ (Φ₁ x p ∨ Φ₂ x p)) → (w = y ∨ (Φ₁ w y ∨ Φ₂ w y)) →
      Φ₁ x y ∧ (E x y → x = p ∧ y = q))
    (c2 : ∀ w, W w → ∀ x y, (x = w ∨ (Φ₁ x w ∨ Φ₂ x w)) → (q = y ∨ (Φ₁ q y ∨ Φ₂ q y)) →
      Φ₂ x y ∧ (E x y → x = p ∧ y = q))
    (χ : Gn g N → ℂ) (hχ : IsClass χ) : tr (ePat g N Φ₁ E ψ) χ = tr (ePat g N Φ₂ E ψ) χ := by
  obtain ⟨⟨H₁, hH₁, hc₁⟩, hu₁, ha₁⟩ := GlobalTheory.T.patternGroup_subgroup_order_character g N Φ₁ i1 t1
  obtain ⟨⟨H₂, hH₂, hc₂⟩, hu₂, ha₂⟩ := GlobalTheory.T.patternGroup_subgroup_order_character g N Φ₂ i2 t2
  obtain ⟨⟨H, hH, -⟩, -, -⟩ :=
    GlobalTheory.T.patternGroup_subgroup_order_character g N (fun a b => Φ₁ a b ∨ Φ₂ a b) (fun a h => h.elim (i1 a) (i2 a)) t0
  have hm₁ : ∀ x y : H₁, sumAt E (((x : Gn g N) : Mt g N) * ((y : Gn g N) : Mt g N)) =
      sumAt E ((x : Gn g N) : Mt g N) + sumAt E ((y : Gn g N) : Mt g N) :=
    fun x y => ha₁ E e1 hE _ _ ((hH₁ _).1 x.2) ((hH₁ _).1 y.2)
  have hm₂ : ∀ x y : H₂, sumAt E (((x : Gn g N) : Mt g N) * ((y : Gn g N) : Mt g N)) =
      sumAt E ((x : Gn g N) : Mt g N) + sumAt E ((y : Gn g N) : Mt g N) :=
    fun x y => ha₂ E e2 hE _ _ ((hH₂ _).1 x.2) ((hH₂ _).1 y.2)
  have hle₁ : H₁ ≤ H := fun x hx => (hH x).2 fun a b hab => (hH₁ x).1 hx a b fun h' => hab (Or.inl h')
  have hle₂ : H₂ ≤ H := fun x hx => (hH x).2 fun a b hab => (hH₂ x).1 hx a b fun h' => hab (Or.inr h')
  have hsplit : ∀ A B : Fin N → Fin N → Prop,
      (Finset.univ.filter fun r : Fin N × Fin N => A r.1 r.2).card =
        (Finset.univ.filter fun r : Fin N × Fin N => A r.1 r.2 ∧ B r.1 r.2).card +
          (Finset.univ.filter fun r : Fin N × Fin N => A r.1 r.2 ∧ ¬ B r.1 r.2).card := by
    intro A B
    rw [← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter fun r : Fin N × Fin N => A r.1 r.2)
      (fun r : Fin N × Fin N => B r.1 r.2), Finset.filter_filter, Finset.filter_filter]
  have hcount : (Finset.univ.filter fun r : Fin N × Fin N => Φ₁ r.1 r.2).card =
      (Finset.univ.filter fun r : Fin N × Fin N => Φ₂ r.1 r.2).card := by
    rw [hsplit Φ₁ Φ₂, hsplit Φ₂ Φ₁]
    congr 1
    · congr 1
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact and_comm
    · have e₁ : (Finset.univ.filter fun r : Fin N × Fin N => Φ₁ r.1 r.2 ∧ ¬ Φ₂ r.1 r.2) =
          Finset.univ.filter fun r : Fin N × Fin N => r.1 = p ∧ W r.2 :=
        Finset.filter_congr fun r _ => d1 r.1 r.2
      have e₂ : (Finset.univ.filter fun r : Fin N × Fin N => Φ₂ r.1 r.2 ∧ ¬ Φ₁ r.1 r.2) =
          Finset.univ.filter fun r : Fin N × Fin N => W r.1 ∧ r.2 = q :=
        Finset.filter_congr fun r _ => d2 r.1 r.2
      rw [e₁, e₂, card_filter_fst_eq_and_snd, card_filter_fst_and_snd_eq]
  have hcard : Nat.card H₁ = Nat.card H₂ := by rw [hc₁, hc₂, hcount]
  have heq : ∀ (a : H₁) (b : H₂), (a : Gn g N) = b → patChar ψ E hE H₁ hm₁ a = patChar ψ E hE H₂ hm₂ b :=
    fun a b hab => Units.ext (by rw [patChar_val, patChar_val, hab])
  have hx₁ : ∀ h ∈ H, h ∉ H₁ → ∃ a a' : H₁, (a' : Gn g N) = h⁻¹ * a * h ∧
      patChar ψ E hE H₁ hm₁ a' ≠ patChar ψ E hE H₁ hm₁ a := by
    intro h hh hh₁
    have hB := (hH h).1 hh
    have hA := (hH h⁻¹).1 (H.inv_mem hh)
    obtain ⟨w, hw, hwq⟩ : ∃ w, W w ∧ (h : Mt g N) w q ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hh₁
      rw [hH₁]
      intro a b hab
      by_cases h2 : Φ₂ a b
      · obtain ⟨ha, rfl⟩ := (d2 a b).1 ⟨h2, hab⟩
        rw [hc a ha, Matrix.one_apply_ne fun e => hq (by rw [← e]; exact ha)]
      · exact hB a b fun h' => h'.elim hab h2
    have hpp : ((h⁻¹ : Gn g N) : Mt g N) p p = 1 := by
      rw [hA p p fun h' => h'.elim (i1 p) (i2 p), Matrix.one_apply_eq]
    exact exists_conj (Φ := fun a b => Φ₁ a b ∨ Φ₂ a b) ψ hψ hE hpq (c1 w hw) hu₁
      (Or.inr fun e => hq (by rw [← e]; exact hw)) H₁ hH₁ hm₁ h hA hB (by rw [hpp, one_mul]; exact hwq)
  have hx₂ : ∀ h ∈ H, h ∉ H₂ → ∃ b b' : H₂, (b' : Gn g N) = h⁻¹ * b * h ∧
      patChar ψ E hE H₂ hm₂ b' ≠ patChar ψ E hE H₂ hm₂ b := by
    intro h hh hh₂
    have hB := (hH h).1 hh
    have hA := (hH h⁻¹).1 (H.inv_mem hh)
    obtain ⟨w, hw, hpw⟩ : ∃ w, W w ∧ ((h⁻¹ : Gn g N) : Mt g N) p w ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hh₂
      rw [← inv_mem_iff, hH₂]
      intro a b hab
      by_cases h1 : Φ₁ a b
      · obtain ⟨rfl, hb⟩ := (d1 a b).1 ⟨h1, hab⟩
        rw [hc b hb, Matrix.one_apply_ne fun e => hp (by rw [e]; exact hb)]
      · exact hA a b fun h' => h'.elim h1 hab
    have hqq : (h : Mt g N) q q = 1 := by
      rw [hB q q fun h' => h'.elim (i1 q) (i2 q), Matrix.one_apply_eq]
    exact exists_conj (Φ := fun a b => Φ₁ a b ∨ Φ₂ a b) ψ hψ hE hpq (c2 w hw) hu₂
      (Or.inl fun e => hp (by rw [e]; exact hw)) H₂ hH₂ hm₂ h hA hB (by rw [hqq, mul_one]; exact hpw)
  rw [tr_ePat ψ Φ₁ E H₁ hH₁ χ, tr_ePat ψ Φ₂ E H₂ hH₂ χ]
  have key := GlobalTheory.T.isotypic_trace_eq_of_one_double_coset (Gn g N) H H₁ H₂ (patChar ψ E hE H₁ hm₁) (patChar ψ E hE H₂ hm₂)
    hle₁ hle₂ hcard heq hx₁ hx₂ χ hχ
  simpa only [Units.val_inv_eq_inv_val, patChar_val] using key

section Combinatorics

variable {k s i : ℕ}

theorem phI_trans (hs : i ≤ s) (a b c : Fin N) (h : phI k s i a b) (h' : phI k s i b c) : phI k s i a c := by
  simp only [phI, IsW, Fin.lt_def] at *
  omega

theorem phI_free (hs : i ≤ s) (a b c : Fin N) (h : phI k s i a b) (h' : phI k s i b c) : ¬ eeI k s a c := by
  simp only [phI, eeI, IsW, Fin.lt_def] at *
  omega

theorem phI_irrefl (hs : i ≤ s) (a : Fin N) : ¬ phI k s i a a := by
  simp only [phI, IsW, Fin.lt_def] at *
  omega

theorem phI_union (h1 : 1 ≤ i) (hs : i ≤ s) (a b : Fin N) : (phI k s i a b ∨ phI k s (i - 1) a b) ↔
    (IsW k s a ∧ IsW k s b ∧ a < b) ∨ (¬ IsW k s a ∧ ¬ IsW k s b ∧ a < b) ∨ ((a : ℕ) < i ∧ IsW k s b) ∨
      (IsW k s a ∧ ¬ IsW k s b ∧ i ≤ (b : ℕ)) := by
  simp only [phI, IsW, Fin.lt_def]
  constructor <;> intro h <;> omega

theorem phI_union_trans (h1 : 1 ≤ i) (hs : i ≤ s) (a b c : Fin N) (h : (phI k s i a b ∨ phI k s (i - 1) a b))
    (h' : (phI k s i b c ∨ phI k s (i - 1) b c)) : (phI k s i a c ∨ phI k s (i - 1) a c) := by
  rw [phI_union h1 hs] at h h' ⊢
  simp only [IsW, Fin.lt_def] at h h' ⊢
  omega

theorem phI_diff₁ (h1 : 1 ≤ i) (hs : i ≤ s) {p : Fin N} (hp : (p : ℕ) = i - 1) (a b : Fin N) :
    (phI k s i a b ∧ ¬ phI k s (i - 1) a b) ↔ (a = p ∧ IsW k s b) := by
  simp only [phI, IsW, Fin.lt_def, Fin.ext_iff] at *
  constructor <;> intro h <;> omega

theorem phI_diff₂ (h1 : 1 ≤ i) {q : Fin N} (hq : (i < s ∧ (q : ℕ) = i) ∨ (i = s ∧ (q : ℕ) = s + k))
    (a b : Fin N) : (phI k s (i - 1) a b ∧ ¬ phI k s i a b) ↔ (IsW k s a ∧ b = q) := by
  simp only [phI, IsW, Fin.lt_def, Fin.ext_iff] at *
  constructor <;> intro h <;> omega

theorem phI_conj₁ (h1 : 1 ≤ i) (hs : i ≤ s) {p q : Fin N} (hp : (p : ℕ) = i - 1)
    (hq : (i < s ∧ (q : ℕ) = i) ∨ (i = s ∧ (q : ℕ) = s + k)) (w : Fin N) (hw : IsW k s w) (x y : Fin N)
    (h : x = p ∨ (phI k s i x p ∨ phI k s (i - 1) x p)) (h' : w = y ∨ (phI k s i w y ∨ phI k s (i - 1) w y)) :
    phI k s i x y ∧ (eeI k s x y → x = p ∧ y = q) := by
  rw [phI_union h1 hs] at h h'
  simp only [phI, eeI, IsW, Fin.lt_def, Fin.ext_iff] at h h' hp hq hw ⊢
  refine ⟨?_, fun he => ?_⟩ <;> omega

theorem phI_conj₂ (h1 : 1 ≤ i) (hs : i ≤ s) {p q : Fin N} (hp : (p : ℕ) = i - 1)
    (hq : (i < s ∧ (q : ℕ) = i) ∨ (i = s ∧ (q : ℕ) = s + k)) (w : Fin N) (hw : IsW k s w) (x y : Fin N)
    (h : x = w ∨ (phI k s i x w ∨ phI k s (i - 1) x w)) (h' : q = y ∨ (phI k s i q y ∨ phI k s (i - 1) q y)) :
    phI k s (i - 1) x y ∧ (eeI k s x y → x = p ∧ y = q) := by
  rw [phI_union h1 hs] at h h'
  simp only [phI, eeI, IsW, Fin.lt_def, Fin.ext_iff] at h h' hp hq hw ⊢
  refine ⟨?_, fun he => ?_⟩ <;> omega

end Combinatorics

theorem step : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) , ψ ≠ 1 → ∀ (N k s i : ℕ), N = k + 2 * s + 1 → 1 ≤ i → i ≤ s → ∀ χ : Gn g N → ℂ, IsClass χ → tr (ePat g N (phI k s i) (eeI k s) ψ) χ = tr (ePat g N (phI k s (i - 1)) (eeI k s) ψ) χ := by
  intro g hg ψ hψ N k s i hN h1 hs χ hχ
  obtain ⟨p, hp'⟩ : ∃ p : Fin N, (p : ℕ) = i - 1 := ⟨⟨i - 1, by omega⟩, rfl⟩
  obtain ⟨q, hq'⟩ : ∃ q : Fin N, (i < s ∧ (q : ℕ) = i) ∨ (i = s ∧ (q : ℕ) = s + k) := by
    by_cases hi : i < s
    · exact ⟨⟨i, by omega⟩, Or.inl ⟨hi, rfl⟩⟩
    · exact ⟨⟨s + k, by omega⟩, Or.inr ⟨by omega, rfl⟩⟩
  have hs' : i - 1 ≤ s := by omega
  refine exchange ψ hψ (phI k s i) (phI k s (i - 1)) (eeI k s) (fun a => IsW k s a) p q ?_ ?_ ?_ ?_
    (fun a => phI_irrefl hs a) (fun a => phI_irrefl hs' a) (phI_trans hs) (phI_trans hs')
    (phI_union_trans h1 hs) (phI_free hs) (phI_free hs') (phI_diff₁ h1 hs hp') (phI_diff₂ h1 hq')
    (fun w hw => phI_conj₁ h1 hs hp' hq' w hw) (fun w hw => phI_conj₂ h1 hs hp' hq' w hw) χ hχ
  · intro a ha
    simp only [eeI, IsW] at ha
    omega
  · simp only [eeI, IsW]
    omega
  · intro ha
    simp only [IsW] at ha
    omega
  · intro ha
    simp only [IsW] at ha
    omega

end GlobalTheory.RootExch
