import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlaceRep
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory

namespace DerivFaithful

variable {U A ι : Type} [Ring U] [Algebra ℂ U] [CommRing A] [Algebra ℂ A]

def wordProd (e : ι → U) (l : List ι) : U := (l.map e).prod

def filt (e : ι → U) (d : ℕ) : Submodule ℂ U :=
  Submodule.span ℂ {u | ∃ l : List ι, l.length ≤ d ∧ wordProd e l = u}

lemma wordProd_cons (e : ι → U) (k : ι) (l : List ι) :
    wordProd e (k :: l) = e k * wordProd e l := by simp [wordProd]

lemma wordProd_append (e : ι → U) (l l' : List ι) :
    wordProd e (l ++ l') = wordProd e l * wordProd e l' := by simp [wordProd, List.prod_append]

lemma wordProd_mem_filt (e : ι → U) (l : List ι) : wordProd e l ∈ filt e l.length :=
  Submodule.subset_span ⟨l, le_rfl, rfl⟩

lemma filt_mono (e : ι → U) {d d' : ℕ} (h : d ≤ d') : filt e d ≤ filt e d' := by
  apply Submodule.span_mono
  rintro _ ⟨l, hl, rfl⟩
  exact ⟨l, hl.trans h, rfl⟩

lemma mul_mem_filt (e : ι → U) {i j : ℕ} {x y : U} (hx : x ∈ filt e i) (hy : y ∈ filt e j) :
    x * y ∈ filt e (i + j) := by
  have h : filt e i * filt e j ≤ filt e (i + j) := by
    rw [filt, filt, Submodule.span_mul_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨l, hl, rfl⟩, _, ⟨l', hl', rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨l ++ l', ?_, (wordProd_append e l l')⟩
    simp; omega
  exact h (Submodule.mul_mem_mul hx hy)

lemma span_le_filt_one (e : ι → U) : Submodule.span ℂ (Set.range e) ≤ filt e 1 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  exact Submodule.subset_span ⟨[k], by simp, by simp [wordProd]⟩

lemma der_pow_mem (D : A →ₗ[ℂ] A) (hD : ∀ x y, D (x * y) = D x * y + x * D y) (I : Ideal A) :
    ∀ m : ℕ, ∀ x ∈ I ^ (m + 1), D x ∈ I ^ m := by
  intro m
  induction m with
  | zero => intro x _; simp
  | succ m ih =>
    intro x hx
    rw [pow_succ'] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro p hp q hq
      rw [hD]
      refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hq) ?_
      rw [pow_succ']
      exact Ideal.mul_mem_mul hp (ih q hq)
    · intro p q hp hq
      rw [map_add]
      exact Ideal.add_mem _ hp hq

lemma word_pow_mem (e : ι → U) (π : U →ₐ[ℂ] Module.End ℂ A)
    (hder : ∀ k (x y : A), π (e k) (x * y) = π (e k) x * y + x * π (e k) y) (I : Ideal A) :
    ∀ (w : List ι) (m : ℕ), ∀ x ∈ I ^ (m + w.length), π (wordProd e w) x ∈ I ^ m := by
  intro w
  induction w with
  | nil => intro m x hx; simpa [wordProd] using hx
  | cons k w ih =>
    intro m x hx
    rw [wordProd_cons, map_mul, Module.End.mul_apply]
    apply der_pow_mem (π (e k)) (hder k) I m
    apply ih (m + 1)
    have : m + (k :: w).length = m + 1 + w.length := by simp; omega
    rw [this] at hx; exact hx

lemma filt_vanish (e : ι → U) (π : U →ₐ[ℂ] Module.End ℂ A)
    (hder : ∀ k (x y : A), π (e k) (x * y) = π (e k) x * y + x * π (e k) y) (χ : A →ₐ[ℂ] ℂ)
    (d : ℕ) : ∀ u ∈ filt e d, ∀ x ∈ (RingHom.ker χ) ^ (d + 1), χ (π u x) = 0 := by
  let S : Submodule ℂ U :=
    { carrier := {u | ∀ x ∈ (RingHom.ker χ) ^ (d + 1), χ (π u x) = 0}
      add_mem' := by
        intro p q hp hq x hx
        simp [hp x hx, hq x hx]
      zero_mem' := by intro x _; simp
      smul_mem' := by
        intro c p hp x hx
        simp [hp x hx] }
  have h : filt e d ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨l, hl, rfl⟩ x hx
    have hx' : x ∈ (RingHom.ker χ) ^ (1 + l.length) := Ideal.pow_le_pow_right (by omega) hx
    have := word_pow_mem e π hder (RingHom.ker χ) l 1 x hx'
    simpa using this
  intro u hu
  exact h hu

lemma perm_sub_mem (e : ι → U)
    (hcomm : ∀ a b, e a * e b - e b * e a ∈ Submodule.span ℂ (Set.range e))
    {l l' : List ι} (h : l.Perm l') :
    ∀ d, l.length ≤ d + 1 → wordProd e l - wordProd e l' ∈ filt e d := by
  induction h with
  | nil => intro d _; simp
  | cons x h ih =>
    rename_i l₁ l₂
    intro d hd
    rw [wordProd_cons, wordProd_cons, ← mul_sub]
    cases d with
    | zero =>
      have h0 : l₁ = [] := by
        cases l₁ with
        | nil => rfl
        | cons _ _ => simp at hd
      subst h0
      have h0' : l₂ = [] := List.nil_perm.mp h
      subst h0'
      simp
    | succ d =>
      have := mul_mem_filt e (span_le_filt_one e (Submodule.subset_span ⟨x, rfl⟩))
        (ih d (by simp at hd; omega))
      rw [add_comm] at this
      exact this
  | swap x y l =>
    intro d hd
    simp only [wordProd_cons]
    rw [← mul_assoc, ← mul_assoc, ← sub_mul]
    have h1 := span_le_filt_one e (hcomm y x)
    exact filt_mono e (by simp at hd; omega) (mul_mem_filt e h1 (wordProd_mem_filt e l))
  | trans h₁ h₂ ih₁ ih₂ =>
    intro d hd
    have a1 := ih₁ d hd
    have a2 := ih₂ d (by rw [← h₁.length_eq]; exact hd)
    have := Submodule.add_mem _ a1 a2
    simpa using this

lemma exists_mem_filt (e : ι → U) (hgen : Algebra.adjoin ℂ (Set.range e) = ⊤) (u : U) :
    ∃ d, u ∈ filt e d := by
  let S : Subalgebra ℂ U :=
    { carrier := {u | ∃ d, u ∈ filt e d}
      mul_mem' := by
        rintro p q ⟨i, hp⟩ ⟨j, hq⟩
        exact ⟨i + j, mul_mem_filt e hp hq⟩
      add_mem' := by
        rintro p q ⟨i, hp⟩ ⟨j, hq⟩
        exact ⟨i + j, Submodule.add_mem _ (filt_mono e (by omega) hp) (filt_mono e (by omega) hq)⟩
      algebraMap_mem' := by
        intro c
        refine ⟨0, ?_⟩
        rw [Algebra.algebraMap_eq_smul_one]
        exact Submodule.smul_mem _ c (by simpa [wordProd] using wordProd_mem_filt e []) }
  have h : Algebra.adjoin ℂ (Set.range e) ≤ S :=
    Algebra.adjoin_le (by rintro _ ⟨k, rfl⟩; exact ⟨1, span_le_filt_one e (Submodule.subset_span ⟨k, rfl⟩)⟩)
  rw [hgen] at h
  exact h Algebra.mem_top

def testProd (a : ι → A) (β : Multiset ι) : A := (β.map a).prod

lemma testProd_mem_pow (χ : A →ₐ[ℂ] ℂ) (a : ι → A) (ha : ∀ k, χ (a k) = 0) (β : Multiset ι) :
    testProd a β ∈ (RingHom.ker χ) ^ (Multiset.card β) := by
  induction β using Multiset.induction_on with
  | empty => simp
  | cons b β ih =>
    rw [testProd, Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ']
    exact Ideal.mul_mem_mul (by simpa [RingHom.mem_ker] using ha b) ih

lemma der_testProd [DecidableEq ι] (D : A →ₗ[ℂ] A) (hD : ∀ x y, D (x * y) = D x * y + x * D y)
    (χ : A →ₐ[ℂ] ℂ) (a : ι → A) (ha : ∀ j, χ (a j) = 0) (k : ι)
    (hδ : ∀ j, χ (D (a j)) = if k = j then 1 else 0) (β : Multiset ι) :
    D (testProd a β) - algebraMap ℂ A (β.count k) * testProd a (β.erase k)
      ∈ (RingHom.ker χ) ^ (Multiset.card β) := by
  induction β using Multiset.induction_on with
  | empty => simp
  | cons b β ih =>
    set I := RingHom.ker χ
    set c : ℂ := if k = b then 1 else 0 with hc
    set r := D (a b) - algebraMap ℂ A c with hr
    set s := D (testProd a β) - algebraMap ℂ A (β.count k) * testProd a (β.erase k) with hs
    have hrI : r ∈ I := by simp [I, RingHom.mem_ker, hr, hδ b, c]
    have haI : a b ∈ I := by simpa [I, RingHom.mem_ker] using ha b
    have hxβ := testProd_mem_pow χ a ha β
    have key : D (testProd a (b ::ₘ β)) - algebraMap ℂ A ((b ::ₘ β).count k) * testProd a ((b ::ₘ β).erase k)
        = r * testProd a β + a b * s := by
      have e1 : testProd a (b ::ₘ β) = a b * testProd a β := by simp [testProd]
      rw [e1, hD]
      by_cases hkb : k = b
      · subst hkb
        have hc1 : c = 1 := by simp [c]
        rw [Multiset.count_cons_self, Multiset.erase_cons_head, hr, hs, hc1]
        by_cases hmem : k ∈ β
        · have e2 : testProd a β = a k * testProd a (β.erase k) := by
            conv_lhs => rw [← Multiset.cons_erase hmem]
            simp [testProd]
          rw [e2]; simp only [Nat.cast_add, Nat.cast_one, map_add, map_one]; ring
        · rw [Multiset.count_eq_zero.mpr hmem]; simp; ring
      · have hc0 : c = 0 := by simp [c, hkb]
        rw [Multiset.count_cons_of_ne hkb, Multiset.erase_cons_tail _ (Ne.symm hkb), hr, hs, hc0]
        simp [testProd]; ring
    rw [key, Multiset.card_cons, pow_succ']
    exact Ideal.add_mem _ (Ideal.mul_mem_mul hrI hxβ) (Ideal.mul_mem_mul haI ih)

section Pairing

variable [DecidableEq ι] (e : ι → U)
    (hcomm : ∀ a b, e a * e b - e b * e a ∈ Submodule.span ℂ (Set.range e))
    (π : U →ₐ[ℂ] Module.End ℂ A)
    (hder : ∀ k (x y : A), π (e k) (x * y) = π (e k) x * y + x * π (e k) y)
    (χ : A →ₐ[ℂ] ℂ) (a : ι → A) (ha : ∀ k, χ (a k) = 0)
    (hδ : ∀ i k, χ (π (e i) (a k)) = if i = k then 1 else 0)
include hcomm hder ha hδ

lemma pair_cons (k : ι) (w : List ι) (β : Multiset ι) (hlen : w.length + 1 = Multiset.card β) :
    χ (π (wordProd e (k :: w)) (testProd a β)) =
      (β.count k : ℂ) * χ (π (wordProd e w) (testProd a (β.erase k))) := by
  have hx : testProd a β ∈ (RingHom.ker χ) ^ (w.length + 1) := hlen ▸ testProd_mem_pow χ a ha β
  have hp : (k :: w).Perm (w ++ [k]) := (List.perm_append_singleton k w).symm
  have h1 := filt_vanish e π hder χ w.length _ (perm_sub_mem e hcomm hp w.length (by simp)) _ hx
  have e1 : wordProd e (k :: w) =
      (wordProd e (k :: w) - wordProd e (w ++ [k])) + wordProd e (w ++ [k]) := by abel
  rw [e1, map_add, LinearMap.add_apply, map_add, h1, zero_add, wordProd_append, map_mul,
    Module.End.mul_apply]
  have hD := der_testProd (π (e k)) (hder k) χ a ha k (fun j => hδ k j) β
  rw [← hlen] at hD
  have e2 : π (wordProd e [k]) (testProd a β) =
      (π (e k) (testProd a β) - algebraMap ℂ A (β.count k) * testProd a (β.erase k)) +
        algebraMap ℂ A (β.count k) * testProd a (β.erase k) := by simp [wordProd]
  rw [e2, map_add, map_add, filt_vanish e π hder χ w.length _ (wordProd_mem_filt e w) _ hD, zero_add,
    ← Algebra.smul_def, map_smul, map_smul, smul_eq_mul]

lemma pair_ne_zero_iff : ∀ (w : List ι) (β : Multiset ι), w.length = Multiset.card β →
    (χ (π (wordProd e w) (testProd a β)) ≠ 0 ↔ (w : Multiset ι) = β) := by
  intro w
  induction w with
  | nil =>
    intro β hβ
    have : β = 0 := Multiset.card_eq_zero.mp hβ.symm
    subst this
    simp [wordProd, testProd]
  | cons k w ih =>
    intro β hβ
    rw [pair_cons e hcomm π hder χ a ha hδ k w β (by simpa using hβ)]
    by_cases hk : k ∈ β
    · have hcard : w.length = Multiset.card (β.erase k) := by
        rw [Multiset.card_erase_of_mem hk, Nat.pred_eq_sub_one]; simp at hβ; omega
      rw [mul_ne_zero_iff, ih _ hcard]
      have hcnt : (β.count k : ℂ) ≠ 0 := by exact_mod_cast (Multiset.count_ne_zero.mpr hk)
      simp only [hcnt, ne_eq, not_false_eq_true, true_and]
      rw [← Multiset.cons_coe]
      constructor
      · intro h; rw [h, Multiset.cons_erase hk]
      · intro h; rw [← h]; simp
    · have hcnt : β.count k = 0 := Multiset.count_eq_zero.mpr hk
      simp only [hcnt, Nat.cast_zero, zero_mul, ne_eq, not_true_eq_false, false_iff]
      intro h; apply hk; rw [← h]; simp

lemma step_down [Fintype ι] (d : ℕ) (u : U)
    (hu : u ∈ filt e (d + 1)) (hz : ∀ x : A, χ (π u x) = 0) : u ∈ filt e d := by
  let W : Sym ι (d + 1) → U := fun s => wordProd e (s : Multiset ι).toList
  let G : Submodule ℂ U := Submodule.span ℂ (Set.range W)
  have hle : filt e (d + 1) ≤ filt e d ⊔ G := by
    apply Submodule.span_le.mpr
    rintro _ ⟨l, hl, rfl⟩
    rcases Nat.lt_or_ge l.length (d + 1) with h | h
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨l, by omega, rfl⟩)
    · have hl' : l.length = d + 1 := by omega
      let s : Sym ι (d + 1) := ⟨(l : Multiset ι), by simpa using hl'⟩
      have hp : l.Perm (s : Multiset ι).toList := by
        rw [← Multiset.coe_eq_coe, Multiset.coe_toList]; rfl
      have hdiff := perm_sub_mem e hcomm hp d (by omega)
      have e1 : wordProd e l = (wordProd e l - W s) + W s := by abel
      rw [e1]
      exact Submodule.add_mem _ (Submodule.mem_sup_left hdiff)
        (Submodule.mem_sup_right (Submodule.subset_span ⟨s, rfl⟩))
  obtain ⟨v, hv, t, ht, rfl⟩ := Submodule.mem_sup.mp (hle hu)
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp ht
  have hc : ∀ s0, c s0 = 0 := by
    intro s0
    have hx : testProd a (s0 : Multiset ι) ∈ (RingHom.ker χ) ^ (d + 1) := by
      have := testProd_mem_pow χ a ha (s0 : Multiset ι)
      rwa [show Multiset.card (s0 : Multiset ι) = d + 1 from s0.2] at this
    have h1 := hz (testProd a (s0 : Multiset ι))
    rw [map_add, LinearMap.add_apply, map_add, filt_vanish e π hder χ d v hv _ hx, zero_add] at h1
    rw [map_sum, LinearMap.sum_apply, map_sum] at h1
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
    rw [Finset.sum_eq_single s0] at h1
    · have hne := (pair_ne_zero_iff e hcomm π hder χ a ha hδ ((s0 : Multiset ι).toList) s0
        (by simp [s0.2])).mpr (by simp)
      exact (mul_eq_zero.mp h1).resolve_right hne
    · intro s _ hs
      have hiff := pair_ne_zero_iff e hcomm π hder χ a ha hδ ((s : Multiset ι).toList) s0
        (by simp [s.2, s0.2])
      have h0 : χ (π (W s) (testProd a s0)) = 0 := by
        by_contra hh
        exact hs (Sym.coe_injective (by simpa using hiff.mp hh))
      rw [h0, mul_zero]
    · simp
  simp [hc, hv]

end Pairing

end DerivFaithful

open DerivFaithful in

theorem faithful_of_derivations_dual_family : ∀ (U A ι : Type) [Ring U] [Algebra ℂ U] [CommRing A] [Algebra ℂ A] [Fintype ι] [DecidableEq ι] (e : ι → U), Algebra.adjoin ℂ (Set.range e) = ⊤ → (∀ a b, e a * e b - e b * e a ∈ Submodule.span ℂ (Set.range e)) → ∀ (π : U →ₐ[ℂ] Module.End ℂ A), (∀ k (x y : A), π (e k) (x * y) = π (e k) x * y + x * π (e k) y) → ∀ (χ : A →ₐ[ℂ] ℂ) (a : ι → A), (∀ k, χ (a k) = 0) → (∀ i k, χ (π (e i) (a k)) = if i = k then 1 else 0) → ∀ u : U, (∀ x : A, χ (π u x) = 0) → u = 0 := by
  intro U A ι _ _ _ _ _ _ e hgen hcomm π hder χ a ha hδ u hu
  obtain ⟨d, hd⟩ := exists_mem_filt e hgen u
  have h0 : u ∈ filt e 0 := by
    induction d with
    | zero => exact hd
    | succ d ih => exact ih (step_down e hcomm π hder χ a ha hδ d u hd hu)
  have hle : filt e 0 ≤ Submodule.span ℂ {(1 : U)} := by
    apply Submodule.span_le.mpr
    rintro _ ⟨l, hl, rfl⟩
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [wordProd]
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (hle h0)
  have := hu 1
  simp at this
  simp [this]

end GlobalTheory
