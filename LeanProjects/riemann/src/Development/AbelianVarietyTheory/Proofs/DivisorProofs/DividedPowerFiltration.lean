import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish

set_option autoImplicit false

open DividedPowers GlobalTheory.Cris

namespace GlobalTheory.Cris.ExpBij

variable {B : Type} [CommRing B] {J : Ideal B}

def dpFil (δ : DividedPowers J) (m : ℕ) : Ideal B :=
  Ideal.span {x | ∃ l : List (ℕ × B), (∀ p ∈ l, p.2 ∈ J) ∧ m ≤ (l.map Prod.fst).sum ∧
    x = (l.map fun p ↦ δ.dpow p.1 p.2).prod}

variable (δ : DividedPowers J)

set_option autoImplicit false in
open DividedPowers in
variable {B : Type} [CommRing B] {J : Ideal B} in
variable (δ : DividedPowers J) in

theorem _root_.GlobalTheory.Cris.ExpBij.dpFil_anti {m n : ℕ} (h : m ≤ n) :
    _root_.GlobalTheory.Cris.ExpBij.dpFil δ n ≤ _root_.GlobalTheory.Cris.ExpBij.dpFil δ m := by
  refine Ideal.span_mono ?_
  rintro x ⟨l, hl, hs, rfl⟩
  exact ⟨l, hl, h.trans hs, rfl⟩

set_option autoImplicit false in
open DividedPowers in
variable {B : Type} [CommRing B] {J : Ideal B} in
variable (δ : DividedPowers J) in

theorem _root_.GlobalTheory.Cris.ExpBij.mem_dpFil_zero (a : B) : a ∈ _root_.GlobalTheory.Cris.ExpBij.dpFil δ 0 := by
  have h1 : (1 : B) ∈ _root_.GlobalTheory.Cris.ExpBij.dpFil δ 0 :=
    Ideal.subset_span ⟨[], by simp, by simp, by simp⟩
  simpa using Ideal.mul_mem_left _ a h1

set_option autoImplicit false in
open DividedPowers in
variable {B : Type} [CommRing B] {J : Ideal B} in
variable (δ : DividedPowers J) in

theorem _root_.GlobalTheory.Cris.ExpBij.mul_mem_dpFil {m n : ℕ} {a b : B} (ha : a ∈ _root_.GlobalTheory.Cris.ExpBij.dpFil δ m)
    (hb : b ∈ _root_.GlobalTheory.Cris.ExpBij.dpFil δ n) :
    a * b ∈ _root_.GlobalTheory.Cris.ExpBij.dpFil δ (m + n) := by
  have key : _root_.GlobalTheory.Cris.ExpBij.dpFil δ m * _root_.GlobalTheory.Cris.ExpBij.dpFil δ n ≤
      _root_.GlobalTheory.Cris.ExpBij.dpFil δ (m + n) := by
    unfold _root_.GlobalTheory.Cris.ExpBij.dpFil
    rw [Ideal.span_mul_span']
    refine Ideal.span_mono ?_
    rintro _ ⟨x, ⟨l₁, hl₁, hs₁, rfl⟩, y, ⟨l₂, hl₂, hs₂, rfl⟩, rfl⟩
    refine ⟨l₁ ++ l₂, ?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_append.1 hp with hp | hp
      exacts [hl₁ p hp, hl₂ p hp]
    · simp only [List.map_append, List.sum_append]
      omega
    · simp [List.map_append, List.prod_append]
  exact key (Ideal.mul_mem_mul ha hb)

set_option autoImplicit false in
open DividedPowers in
variable {B : Type} [CommRing B] {J : Ideal B} in
variable (δ : DividedPowers J) in

theorem _root_.GlobalTheory.Cris.ExpBij.pow_mem_dpFil {m : ℕ} {a : B} (ha : a ∈ _root_.GlobalTheory.Cris.ExpBij.dpFil δ m)
    (n : ℕ) : a ^ n ∈ _root_.GlobalTheory.Cris.ExpBij.dpFil δ (n * m) := by
  induction n with
  | zero => simpa using _root_.GlobalTheory.Cris.ExpBij.mem_dpFil_zero δ (1 : B)
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact _root_.GlobalTheory.Cris.ExpBij.mul_mem_dpFil δ ih ha

set_option autoImplicit false in
open DividedPowers in
variable {B : Type} [CommRing B] {J : Ideal B} in
variable (δ : DividedPowers J) in

theorem _root_.GlobalTheory.Cris.ExpBij.dpow_mem_dpFil {a : B} (ha : a ∈ J) (n : ℕ) :
    δ.dpow n a ∈ _root_.GlobalTheory.Cris.ExpBij.dpFil δ n :=
  Ideal.subset_span ⟨[(n, a)], by simpa using ha, by simp, by simp⟩

theorem exists_widePullback_of_iteratedLine (l : List (ℕ × B)) (hl : ∀ p ∈ l, p.2 ∈ J) (h1 : 1 ≤ (l.map Prod.fst).sum) :
    (l.map fun p ↦ δ.dpow p.1 p.2).prod ∈ J ∧
      ∀ n, δ.dpow n (l.map fun p ↦ δ.dpow p.1 p.2).prod ∈ dpFil δ (n * (l.map Prod.fst).sum) := by
  induction l with
  | nil => simp at h1
  | cons p l ih =>
    have hp : p.2 ∈ J := hl p (by simp)
    have hl' : ∀ q ∈ l, q.2 ∈ J := fun q hq ↦ hl q (by simp [hq])
    simp only [List.map_cons, List.sum_cons, List.prod_cons] at h1 ⊢
    by_cases h0 : p.1 = 0
    · rw [h0, δ.dpow_zero hp, one_mul, zero_add]
      exact ih hl' (by omega)
    · have hm := δ.dpow_mem h0 hp
      refine ⟨J.mul_mem_right _ hm, fun n ↦ ?_⟩
      rw [δ.dpow_mul_right hm, δ.dpow_comp h0 hp, mul_add]
      exact mul_mem_dpFil δ (Ideal.mul_mem_left _ _ (dpow_mem_dpFil δ hp _))
        (pow_mem_dpFil δ (Ideal.subset_span ⟨l, hl', le_rfl, rfl⟩) n)

set_option autoImplicit false in
open DividedPowers in
variable {B : Type} [CommRing B] {J : Ideal B} in
variable (δ : DividedPowers J) in

theorem _root_.GlobalTheory.Cris.ExpBij.dpFil_le {m : ℕ} (hm : 1 ≤ m) : _root_.GlobalTheory.Cris.ExpBij.dpFil δ m ≤ J := by
  refine Ideal.span_le.2 ?_
  rintro x ⟨l, hl, hs, rfl⟩
  have hex : ∃ p ∈ l, p.1 ≠ 0 := by
    by_contra h
    push_neg at h
    have hzero : (l.map Prod.fst).sum = 0 := by
      refine List.sum_eq_zero fun x hx => ?_
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      exact h p hp
    omega
  obtain ⟨p, hp, hp0⟩ := hex
  obtain ⟨c, hc⟩ := List.dvd_prod (List.mem_map.2 ⟨p, hp, rfl⟩ :
    δ.dpow p.1 p.2 ∈ l.map fun p ↦ δ.dpow p.1 p.2)
  rw [SetLike.mem_coe, hc]
  exact J.mul_mem_right _ (δ.dpow_mem hp0 (hl p hp))

set_option autoImplicit false in
open DividedPowers in
variable {B : Type} [CommRing B] {J : Ideal B} in
variable (δ : DividedPowers J) in

theorem _root_.GlobalTheory.Cris.ExpBij.mem_dpFil_one {a : B} (ha : a ∈ J) : a ∈ _root_.GlobalTheory.Cris.ExpBij.dpFil δ 1 := by
  have h := _root_.GlobalTheory.Cris.ExpBij.dpow_mem_dpFil δ ha 1
  rwa [δ.dpow_one ha] at h

set_option autoImplicit false in
open DividedPowers in
variable {B : Type} [CommRing B] {J : Ideal B} in
variable (δ : DividedPowers J) in

theorem _root_.GlobalTheory.Cris.ExpBij.dpow_mem_dpFil_mul {m : ℕ} (hm : 1 ≤ m) {a : B}
    (ha : a ∈ _root_.GlobalTheory.Cris.ExpBij.dpFil δ m) (n : ℕ) :
    δ.dpow n a ∈ _root_.GlobalTheory.Cris.ExpBij.dpFil δ (n * m) := by
  have hgen : ∀ l : List (ℕ × B), (∀ p ∈ l, p.2 ∈ J) → ∀ n,
      δ.dpow n (l.map fun p ↦ δ.dpow p.1 p.2).prod ∈
        _root_.GlobalTheory.Cris.ExpBij.dpFil δ (n * (l.map Prod.fst).sum) := by
    intro l
    induction l with
    | nil =>
      intro _ n
      simp only [List.map_nil, List.sum_nil, mul_zero]
      exact _root_.GlobalTheory.Cris.ExpBij.mem_dpFil_zero δ _
    | cons p l ih =>
      intro hl n
      have hp : p.2 ∈ J := hl p List.mem_cons_self
      have hl' : ∀ q ∈ l, q.2 ∈ J := fun q hq => hl q (List.mem_cons_of_mem _ hq)
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      by_cases hk : p.1 = 0
      · rw [hk, δ.dpow_zero hp, one_mul, zero_add]
        exact ih hl' n
      · rw [mul_comm (δ.dpow p.1 p.2), δ.dpow_mul (δ.dpow_mem hk hp), δ.dpow_comp hk hp]
        have hy : (l.map fun q ↦ δ.dpow q.1 q.2).prod ∈
            _root_.GlobalTheory.Cris.ExpBij.dpFil δ (l.map Prod.fst).sum :=
          Ideal.subset_span ⟨l, hl', le_rfl, rfl⟩
        have h1 := _root_.GlobalTheory.Cris.ExpBij.pow_mem_dpFil δ hy n
        have h2 : (↑(n.uniformBell p.1) : B) * δ.dpow (n * p.1) p.2 ∈
            _root_.GlobalTheory.Cris.ExpBij.dpFil δ (n * p.1) :=
          Ideal.mul_mem_left _ _ (_root_.GlobalTheory.Cris.ExpBij.dpow_mem_dpFil δ hp _)
        have h3 := _root_.GlobalTheory.Cris.ExpBij.mul_mem_dpFil δ h1 h2
        rw [show n * (p.1 + (l.map Prod.fst).sum) = n * (l.map Prod.fst).sum + n * p.1 by ring]
        exact h3
  have hJ : ∀ x ∈ _root_.GlobalTheory.Cris.ExpBij.dpFil δ m, x ∈ J :=
    fun x hx => _root_.GlobalTheory.Cris.ExpBij.dpFil_le δ hm hx
  revert n
  unfold _root_.GlobalTheory.Cris.ExpBij.dpFil at ha
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, hs, rfl⟩ := hx
    intro n
    exact _root_.GlobalTheory.Cris.ExpBij.dpFil_anti δ (Nat.mul_le_mul_left n hs) (hgen l hl n)
  | zero =>
    intro n
    rcases n with _ | n
    · rw [zero_mul]
      exact _root_.GlobalTheory.Cris.ExpBij.mem_dpFil_zero δ _
    · rw [δ.dpow_eval_zero (Nat.succ_ne_zero n)]
      exact zero_mem _
  | add x y hx hy ihx ihy =>
    intro n
    rw [δ.dpow_add (hJ x hx) (hJ y hy)]
    refine Ideal.sum_mem _ fun k hk => ?_
    have hsum := Finset.HasAntidiagonal.mem_antidiagonal.1 hk
    rw [← hsum, add_mul]
    exact _root_.GlobalTheory.Cris.ExpBij.mul_mem_dpFil δ (ihx k.1) (ihy k.2)
  | smul b x hx ihx =>
    intro n
    rw [smul_eq_mul, δ.dpow_mul (hJ x hx)]
    exact Ideal.mul_mem_left _ _ (ihx n)

variable {δ}

theorem exists_dpFil_eq_bot (h : IsNilDP δ) : ∃ N, dpFil δ N = ⊥ := by
  obtain ⟨N, h⟩ := h
  refine ⟨N, Ideal.span_eq_bot.2 ?_⟩
  rintro _ ⟨l, h1, h2, rfl⟩
  exact h l h1 h2

set_option autoImplicit false in
open DividedPowers in
variable {B : Type} [CommRing B] {J : Ideal B} in
variable (δ : DividedPowers J) in
variable {δ} in

theorem _root_.GlobalTheory.Cris.ExpBij.dpExp_bijOn : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J),
    _root_.GlobalTheory.Cris.IsNilDP δ → Set.BijOn (_root_.GlobalTheory.Cris.dpExp δ) (J : Set B) {u | u - 1 ∈ J} := by
  intro B _ J δ hδ
  obtain ⟨N, hN⟩ := id hδ
  have hbot : _root_.GlobalTheory.Cris.ExpBij.dpFil δ N = ⊥ := by
    refine le_bot_iff.1 (Ideal.span_le.2 ?_)
    rintro x ⟨l, hl, hs, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_bot]
    exact hN l hl hs
  have hvan : ∀ a ∈ J, ∀ n, N ≤ n → δ.dpow n a = 0 := fun a ha n hn => by
    simpa using hN [(n, a)] (by simpa using ha) (by simpa using hn)
  have hexp : ∀ a ∈ J, _root_.GlobalTheory.Cris.dpExp δ a = ∑ n ∈ Finset.range (N + 2), δ.dpow n a :=
    fun a ha => _root_.GlobalTheory.Cris.dpExp_eq_sum_range_of_vanish δ a (N + 2) fun n hn => hvan a ha n (by omega)
  have hkey : ∀ k, 1 ≤ k → ∀ c ∈ _root_.GlobalTheory.Cris.ExpBij.dpFil δ k,
      _root_.GlobalTheory.Cris.dpExp δ c - 1 - c ∈ _root_.GlobalTheory.Cris.ExpBij.dpFil δ (k + 1) := by
    intro k hk c hc
    have hcJ := _root_.GlobalTheory.Cris.ExpBij.dpFil_le δ hk hc
    rw [hexp c hcJ, Finset.sum_range_succ', Finset.sum_range_succ', δ.dpow_zero hcJ]
    have h1 : δ.dpow (0 + 1) c = c := by
      rw [zero_add]
      exact δ.dpow_one hcJ
    rw [h1, show ∀ s : B, s + c + 1 - 1 - c = s from fun s => by ring]
    refine Ideal.sum_mem _ fun i _ => ?_
    exact _root_.GlobalTheory.Cris.ExpBij.dpFil_anti δ (by nlinarith)
      (_root_.GlobalTheory.Cris.ExpBij.dpow_mem_dpFil_mul δ hk hc (i + 1 + 1))
  have hJ1 : ∀ x ∈ J, x ∈ _root_.GlobalTheory.Cris.ExpBij.dpFil δ 1 := fun x hx =>
    _root_.GlobalTheory.Cris.ExpBij.mem_dpFil_one δ hx
  have hmaps : ∀ a ∈ J, _root_.GlobalTheory.Cris.dpExp δ a - 1 ∈ J := by
    intro a ha
    have h2 := _root_.GlobalTheory.Cris.ExpBij.dpFil_le δ (by norm_num) (hkey 1 le_rfl a (hJ1 a ha))
    have h3 := J.add_mem h2 ha
    rwa [sub_add_cancel] at h3
  refine ⟨fun a ha => hmaps a ha, ?_, ?_⟩
  · intro a ha b hb hab
    have hzero : ∀ c ∈ J, _root_.GlobalTheory.Cris.dpExp δ c = 1 → c = 0 := by
      intro c hc h1
      have hall : ∀ k, 1 ≤ k → c ∈ _root_.GlobalTheory.Cris.ExpBij.dpFil δ k := by
        intro k hk
        induction k, hk using Nat.le_induction with
        | base => exact hJ1 c hc
        | succ k hk ih =>
          have h := neg_mem (hkey k hk c ih)
          rw [h1] at h
          simpa using h
      have hc' := _root_.GlobalTheory.Cris.ExpBij.dpFil_anti δ (Nat.le_succ N) (hall (N + 1) (by omega))
      rw [hbot] at hc'
      exact (Submodule.mem_bot _).1 hc'
    have hsum : _root_.GlobalTheory.Cris.dpExp δ (b + -a) = 1 := by
      rw [hδ.dpExp_add_eq_mul hb (J.neg_mem ha), ← hab, ← hδ.dpExp_add_eq_mul ha (J.neg_mem ha),
        add_neg_cancel, _root_.GlobalTheory.Cris.dpExp_zero]
    exact (add_neg_eq_zero.1 (hzero (b + -a) (J.add_mem hb (J.neg_mem ha)) hsum)).symm
  · intro u hu
    have hu' : u - 1 ∈ J := hu
    have happrox : ∀ k, 1 ≤ k → ∃ a ∈ J, _root_.GlobalTheory.Cris.dpExp δ a - u ∈ _root_.GlobalTheory.Cris.ExpBij.dpFil δ k := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base =>
        refine ⟨0, J.zero_mem, ?_⟩
        rw [_root_.GlobalTheory.Cris.dpExp_zero]
        apply hJ1
        have h := J.neg_mem hu'
        rwa [neg_sub] at h
      | succ k hk ih =>
        obtain ⟨a, ha, hd⟩ := ih
        obtain ⟨d, hd_eq⟩ : ∃ d, d = _root_.GlobalTheory.Cris.dpExp δ a - u := ⟨_, rfl⟩
        rw [← hd_eq] at hd
        have hdJ : d ∈ J := _root_.GlobalTheory.Cris.ExpBij.dpFil_le δ hk hd
        refine ⟨a + -d, J.add_mem ha (J.neg_mem hdJ), ?_⟩
        have hr := hkey k hk (-d) (neg_mem hd)
        rw [hδ.dpExp_add_eq_mul ha (J.neg_mem hdJ)]
        have hid : _root_.GlobalTheory.Cris.dpExp δ a * _root_.GlobalTheory.Cris.dpExp δ (-d) - u =
            -((_root_.GlobalTheory.Cris.dpExp δ a - 1) * d) +
              _root_.GlobalTheory.Cris.dpExp δ a * (_root_.GlobalTheory.Cris.dpExp δ (-d) - 1 - -d) := by
          rw [hd_eq]
          ring
        rw [hid]
        refine Ideal.add_mem _ (neg_mem ?_) (Ideal.mul_mem_left _ _ hr)
        have h := _root_.GlobalTheory.Cris.ExpBij.mul_mem_dpFil δ (hJ1 _ (hmaps a ha)) hd
        rwa [show 1 + k = k + 1 from add_comm 1 k] at h
    obtain ⟨a, ha, h⟩ := happrox (N + 1) (by omega)
    have h' := _root_.GlobalTheory.Cris.ExpBij.dpFil_anti δ (Nat.le_succ N) h
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at h'
    exact ⟨a, ha, h'⟩

end GlobalTheory.Cris.ExpBij
