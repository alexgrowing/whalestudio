import Formalism.RealPlaceAnalysis.StatementKT

open scoped InnerProductSpace
open Finset

noncomputable section

namespace Formalism.REAL

theorem compact_weight_orthogonal : KWtOrth := by
  intro V _ _ n ε F μ ν x y hU hx hy hne
  obtain ⟨a, ha⟩ : ∃ a, μ a ≠ ν a := by
    by_contra h; push Not at h; exact hne (funext h)
  have h1 := hU a a rfl x y
  rw [hx a, hy a, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h1
  have h2 : ((μ a : ℂ) - (ν a : ℂ)) * ⟪x, y⟫_ℂ = 0 := by
    rw [sub_mul, h1, sub_self]
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (by exact_mod_cast sub_eq_zero.mp h) ha
  · exact h

section basics
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ V}

theorem mem_compact_span_self (x : V) : x ∈ kSpan ε F x := by
  unfold kSpan; rw [Submodule.mem_sInf]; intro S hS; exact hS.1

theorem compact_span_stable (x : V) : KStable ε F (kSpan ε F x) := by
  intro a b hab y hy
  unfold kSpan at *; rw [Submodule.mem_sInf] at *; intro S hS; exact hS.2 a b hab y (hy S hS)

theorem compact_span_le_stable {x : V} {S : Submodule ℂ V} (hx : x ∈ S) (hS : KStable ε F S) :
    kSpan ε F x ≤ S := sInf_le ⟨hx, hS⟩

theorem compact_lie_commutator (h : KRel ε F) {a b c d : Fin n} (hab : ε a = ε b) (hcd : ε c = ε d) (y : V) :
    F a b (F c d y) - F c d (F a b y) =
      (if b = c then F a d y else 0) - (if d = a then F c b y else 0) := by
  have := LinearMap.congr_fun (h a b c d hab hcd) y
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
  split_ifs at this ⊢ <;> simpa using this

theorem word_action_nil (x : V) : ew F [] x = x := rfl

theorem word_action_cons (p : Fin n × Fin n) (w : List (Fin n × Fin n)) (x : V) :
    ew F (p :: w) x = F p.1 p.2 (ew F w x) := rfl

theorem compact_weight_shift (h : KRel ε F) {ν : Fin n → ℝ} {y : V} (hy : IsWeight F ν y) {c d : Fin n}
    (hcd : ε c = ε d) : IsWeight F (ν + Pi.single c 1 - Pi.single d 1) (F c d y) := by
  intro a
  have := compact_lie_commutator h (a := a) (b := a) rfl hcd y
  rw [hy a, map_smul, sub_eq_iff_eq_add] at this
  rw [this]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  rcases eq_or_ne a c with h1 | h1 <;> rcases eq_or_ne d a with h2 | h2
  · subst h1; subst h2; simp
  · subst h1; simp [h2, Ne.symm h2, add_smul]; abel
  · subst h2; simp [h1, sub_smul]; abel
  · simp [h1, h2, Ne.symm h2]
end basics

section low
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ V}

def wordWeightShift {m : ℕ} : List (Fin m × Fin m) → Fin m → ℝ
  | [] => 0
  | p :: w => Pi.single p.1 1 - Pi.single p.2 1 + wordWeightShift w

def heightFunctional {m : ℕ} (v : Fin m → ℝ) : ℝ := ∑ a : Fin m, ((a : ℕ) : ℝ) * v a

theorem height_functional_add {m : ℕ} (u v : Fin m → ℝ) : heightFunctional (u + v) = heightFunctional u + heightFunctional v := by
  simp [heightFunctional, mul_add, sum_add_distrib]

theorem height_functional_root {m : ℕ} (c d : Fin m) :
    heightFunctional (Pi.single c (1 : ℝ) - Pi.single d 1) = (c : ℝ) - d := by
  simp [heightFunctional, Pi.single_apply, mul_sub, sum_sub_distrib]

theorem height_word_shift_nonneg {m : ℕ} (w : List (Fin m × Fin m)) (hw : ∀ p ∈ w, p.2 < p.1) :
    0 ≤ heightFunctional (wordWeightShift w) ∧ (w ≠ [] → 0 < heightFunctional (wordWeightShift w)) := by
  induction w with
  | nil => simp [wordWeightShift, heightFunctional]
  | cons p w ih =>
    have h1 := ih (fun q hq => hw q (List.mem_cons_of_mem _ hq))
    have h2 : ((p.2 : ℕ) : ℝ) < ((p.1 : ℕ) : ℝ) := by
      exact_mod_cast (hw p List.mem_cons_self)
    simp only [wordWeightShift, height_functional_add, height_functional_root]
    constructor
    · linarith [h1.1]
    · intro _; linarith [h1.1]

theorem word_action_weight (h : KRel ε F) {μ : Fin n → ℝ} {x : V} (hx : IsWeight F μ x)
    (w : List (Fin n × Fin n)) (hw : ∀ p ∈ w, ε p.1 = ε p.2) :
    IsWeight F (μ + wordWeightShift w) (ew F w x) := by
  induction w with
  | nil => simp only [wordWeightShift, add_zero]; exact hx
  | cons p w ih =>
    have := compact_weight_shift h (ih (fun q hq => hw q (List.mem_cons_of_mem _ hq)))
      (hw p List.mem_cons_self)
    have e : μ + wordWeightShift (p :: w) = μ + wordWeightShift w + Pi.single p.1 1 - Pi.single p.2 1 := by
      simp only [wordWeightShift]; abel
    rw [e]; exact this

def heightOperator (F : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ V :=
  ∑ a : Fin n, ((a : ℕ) : ℂ) • F a a

theorem height_operator_weight {ν : Fin n → ℝ} {y : V} (hy : IsWeight F ν y) :
    heightOperator F y = ((heightFunctional ν : ℝ) : ℂ) • y := by
  rw [heightOperator, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, show ∀ a, F a a y = ((ν a : ℝ) : ℂ) • y from hy, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  simp [heightFunctional]

theorem lowering_word_mem_span (x : V) (w : List (Fin n × Fin n)) (hw : ∀ p ∈ w, ε p.1 = ε p.2 ∧ p.2 < p.1) :
    ew F w x ∈ lowSpan ε F x := Submodule.subset_span ⟨w, hw, rfl⟩

theorem self_mem_lowering_span (x : V) : x ∈ lowSpan ε F x := lowering_word_mem_span x [] (by simp)

theorem lowering_operator_mem_span {x : V} {c d : Fin n} (hcd : ε c = ε d) (hdc : d < c) {z : V}
    (hz : z ∈ lowSpan ε F x) : F c d z ∈ lowSpan ε F x := by
  have : lowSpan ε F x ≤ (lowSpan ε F x).comap (F c d) := by
    refine Submodule.span_le.mpr ?_
    rintro y ⟨w, hw, rfl⟩
    show F c d (ew F w x) ∈ lowSpan ε F x
    refine lowering_word_mem_span x ((c, d) :: w) ?_
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨hcd, hdc⟩
    · exact hw p hp
  exact this hz

theorem lowering_word_raises_in_span (h : KRel ε F) {μ : Fin n → ℝ} {x : V} (hx : KHighest ε F μ x)
    (w : List (Fin n × Fin n)) (hw : ∀ p ∈ w, ε p.1 = ε p.2 ∧ p.2 < p.1) :
    ∀ a b, ε a = ε b → F a b (ew F w x) ∈ lowSpan ε F x := by
  induction w with
  | nil =>
    intro a b hab
    rcases lt_trichotomy a b with hlt | heq | hgt
    · rw [word_action_nil, hx.2 a b hlt hab]; exact zero_mem _
    · subst heq; rw [word_action_nil, hx.1 a]; exact Submodule.smul_mem _ _ (self_mem_lowering_span x)
    · refine lowering_word_mem_span x [(a, b)] ?_
      simp [hab, hgt]
  | cons p w ih =>
    have hw' : ∀ q ∈ w, ε q.1 = ε q.2 ∧ q.2 < q.1 := fun q hq => hw q (List.mem_cons_of_mem _ hq)
    have hp := hw p List.mem_cons_self
    intro a b hab
    rcases lt_trichotomy a b with hlt | heq | hgt
    · rw [word_action_cons]
      have hc := compact_lie_commutator h hab hp.1 (ew F w x)
      rw [sub_eq_iff_eq_add] at hc
      rw [hc]
      refine add_mem (sub_mem ?_ ?_) (lowering_operator_mem_span hp.1 hp.2 (ih hw' a b hab))
      · split_ifs with h1
        · exact ih hw' a p.2 (by rw [hab, h1, hp.1])
        · exact zero_mem _
      · split_ifs with h1
        · exact ih hw' p.1 b (by rw [hp.1, h1, hab])
        · exact zero_mem _
    · subst heq
      have hwt := word_action_weight h hx.1 (p :: w) (fun q hq => (hw q hq).1)
      rw [hwt a]; exact Submodule.smul_mem _ _ (lowering_word_mem_span x _ hw)
    · refine lowering_word_mem_span x ((a, b) :: p :: w) ?_
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨hab, hgt⟩
      · exact hw q hq

theorem lowering_span_stable (h : KRel ε F) {μ : Fin n → ℝ} {x : V} (hx : KHighest ε F μ x) :
    KStable ε F (lowSpan ε F x) := by
  intro a b hab z hz
  have : lowSpan ε F x ≤ (lowSpan ε F x).comap (F a b) := by
    refine Submodule.span_le.mpr ?_
    rintro y ⟨w, hw, rfl⟩
    exact lowering_word_raises_in_span h hx w hw a b hab
  exact this hz

theorem compact_span_eq_lowering (h : KRel ε F) {μ : Fin n → ℝ} {x : V} (hx : KHighest ε F μ x) :
    kSpan ε F x = lowSpan ε F x := by
  apply le_antisymm
  · exact compact_span_le_stable (self_mem_lowering_span x) (lowering_span_stable h hx)
  · refine Submodule.span_le.mpr ?_
    rintro y ⟨w, hw, rfl⟩
    induction w with
    | nil => exact mem_compact_span_self x
    | cons p w ih =>
      exact compact_span_stable x p.1 p.2 (hw p List.mem_cons_self).1 _
        (ih (fun q hq => hw q (List.mem_cons_of_mem _ hq)))

theorem lowering_span_weight_scalar (h : KRel ε F) {μ : Fin n → ℝ} {x : V} (hx : KHighest ε F μ x) {y : V}
    (hy : y ∈ lowSpan ε F x) (hyw : IsWeight F μ y) : ∃ c : ℂ, y = c • x := by
  set T := heightOperator F with hT
  set φ0 : ℂ := ((heightFunctional μ : ℝ) : ℂ) with hφ0
  have hle : lowSpan ε F x ≤ (ℂ ∙ x) ⊔ ⨆ l ∈ {l : ℂ | l ≠ φ0}, T.eigenspace l := by
    refine Submodule.span_le.mpr ?_
    rintro z ⟨w, hw, rfl⟩
    rcases w with _ | ⟨p, w⟩
    · exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self x)
    · apply Submodule.mem_sup_right
      have hwt := word_action_weight h hx.1 (p :: w) (fun q hq => (hw q hq).1)
      have hpos := (height_word_shift_nonneg (p :: w) (fun q hq => (hw q hq).2)).2 (List.cons_ne_nil _ _)
      have hmem : ew F (p :: w) x ∈ T.eigenspace ((heightFunctional (μ + wordWeightShift (p :: w)) : ℝ) : ℂ) := by
        rw [Module.End.mem_eigenspace_iff]; exact height_operator_weight hwt
      refine Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem ?_ hmem)
      show _ ≠ _
      rw [height_functional_add, hφ0]
      intro heq
      have := Complex.ofReal_injective heq
      linarith
  obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.mp (hle hy)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy1
  have hy2e : y2 ∈ T.eigenspace φ0 := by
    rw [Module.End.mem_eigenspace_iff]
    have e1 := height_operator_weight hyw
    have e2 := height_operator_weight hx.1
    rw [← hT, ← hφ0] at e1 e2
    rw [map_add, map_smul, e2, smul_add, smul_comm c φ0 x] at e1
    exact add_left_cancel e1
  have hdis := (Module.End.eigenspaces_iSupIndep T).disjoint_biSup
    (y := {l : ℂ | l ≠ φ0}) (x := φ0) (by simp)
  have : y2 = 0 := (Submodule.disjoint_def.mp hdis) y2 hy2e hy2
  exact ⟨c, by rw [this, add_zero]⟩

end low

theorem compact_lowering_holds : KLow := by
  intro V _ _ n ε F μ x h hx
  exact ⟨compact_span_eq_lowering h hx, fun y hy hyw => lowering_span_weight_scalar h hx hy hyw⟩

theorem kOrth_of (hl : KLow) (hw : KWtOrth) : KOrth := by
  intro V _ _ n ε F μ ν x y h hU hx hy hne x' hx' y' hy'
  have base : ∀ z ∈ kSpan ε F y, ⟪x, z⟫_ℂ = 0 := by
    rw [(hl V n ε F ν y h hy).1]
    intro z hz
    have : lowSpan ε F y ≤ (ℂ ∙ x)ᗮ := by
      refine Submodule.span_le.mpr ?_
      rintro u ⟨w, hw', rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
      cases w with
      | nil => exact hw V n ε F μ ν x y hU hx.1 hy.1 hne
      | cons p w =>
        have hp := hw' p List.mem_cons_self
        show ⟪x, F p.1 p.2 (ew F w y)⟫_ℂ = 0
        rw [← hU p.2 p.1 hp.1.symm, hx.2 p.2 p.1 hp.2 hp.1.symm, inner_zero_left]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (this hz)
  rw [(hl V n ε F μ x h hx).1] at hx'
  have : lowSpan ε F x ≤ (kSpan ε F y)ᗮ := by
    refine Submodule.span_le.mpr ?_
    rintro u ⟨w, hw', rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal']
    induction w with
    | nil => exact base
    | cons p w ih =>
      intro z hz
      have hp := hw' p List.mem_cons_self
      show ⟪F p.1 p.2 (ew F w x), z⟫_ℂ = 0
      rw [hU p.1 p.2 hp.1]
      exact ih (fun q hq => hw' q (List.mem_cons_of_mem _ hq)) _
        (compact_span_stable y p.2 p.1 hp.1.symm z hz)
  have h2 := this hx'
  rw [Submodule.mem_orthogonal'] at h2
  exact h2 y' hy'

theorem compact_lie_commute_casimir {A : Type*} [Ring A] {n : ℕ} {ε : Fin n → Bool} {F : Fin n → Fin n → A}
    (h : KRel ε F) {a b : Fin n} (hab : ε a = ε b) : F a b * CasK ε F = CasK ε F * F a b := by
  rw [← sub_eq_zero]
  have key : ∀ c d, F a b * (if ε c = ε d then F c d * F d c else 0) -
      (if ε c = ε d then F c d * F d c else 0) * F a b =
      (if b = c then (if ε c = ε d then F a d * F d c else 0) else 0)
      - (if d = a then (if ε c = ε d then F c b * F d c else 0) else 0)
      + (if b = d then (if ε c = ε d then F c d * F a c else 0) else 0)
      - (if c = a then (if ε c = ε d then F c d * F d b else 0) else 0) := by
    intro c d
    by_cases hcd : ε c = ε d
    · simp only [if_pos hcd]
      have e1 := h a b c d hab hcd
      have e2 := h a b d c hab hcd.symm
      calc F a b * (F c d * F d c) - F c d * F d c * F a b
          = (F a b * F c d - F c d * F a b) * F d c + F c d * (F a b * F d c - F d c * F a b) := by
            noncomm_ring
        _ = _ := by
            rw [e1, e2]
            simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero]
            abel
    · simp [hcd]
  unfold CasK
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp_rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, key]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun c d => if b = c then (if ε c = ε d then F a d * F d c else 0) else 0),
    Finset.sum_comm (f := fun c d => if c = a then (if ε c = ε d then F c d * F d b else 0) else 0)]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, hab]
  abel

section cas
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ V}

theorem compact_casimir_apply (y : V) :
    CasK ε F y = ∑ a, ∑ b, if ε a = ε b then F a b (F b a y) else 0 := by
  unfold CasK
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  split_ifs <;> rfl

theorem compact_casimir_term_highest (h : KRel ε F) {μ : Fin n → ℝ} {x : V} (hx : KHighest ε F μ x) {a b : Fin n}
    (hab : ε a = ε b) :
    F a b (F b a x) = ((if a = b then μ a ^ 2 else if a < b then μ a - μ b else 0 : ℝ) : ℂ) • x := by
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · have := compact_lie_commutator h hab hab.symm x
    rw [hx.2 a b hlt hab, map_zero, sub_zero, if_pos rfl, if_pos rfl, hx.1 a, hx.1 b] at this
    rw [this, if_neg hlt.ne, if_pos hlt]
    push_cast
    rw [sub_smul]
  · rw [hx.1 a, map_smul, hx.1 a, smul_smul, if_pos rfl]
    push_cast
    rw [sq]
  · rw [hx.2 b a hgt hab.symm, map_zero, if_neg hgt.ne', if_neg (not_lt.mpr hgt.le)]
    simp

theorem compact_casimir_value_eq (μ : Fin n → ℝ) :
    (∑ a, ∑ b, (if ε a = ε b then (if a = b then μ a ^ 2 else if a < b then μ a - μ b else 0)
      else 0 : ℝ)) = ckv ε μ := by
  have hr : ∀ a, rhoC ε a = (∑ b, ((if a < b ∧ ε b = ε a then (1 : ℝ) else 0) -
      (if b < a ∧ ε b = ε a then (1 : ℝ) else 0))) / 2 := by
    intro a
    simp only [rhoC, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      Finset.sum_sub_distrib]
  have hR : ckv ε μ = ∑ a, μ a ^ 2 + ∑ a, ∑ b, (if a < b ∧ ε b = ε a then μ a else 0)
      - ∑ a, ∑ b, (if b < a ∧ ε b = ε a then μ a else 0) := by
    unfold ckv nsq dot
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Pi.add_apply, hr a]
    have : (∑ b, (if a < b ∧ ε b = ε a then μ a else 0)) - ∑ b, (if b < a ∧ ε b = ε a then μ a else 0)
        = μ a * ∑ b, ((if a < b ∧ ε b = ε a then (1 : ℝ) else 0) -
          (if b < a ∧ ε b = ε a then (1 : ℝ) else 0)) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      split_ifs <;> ring
    rw [add_sub_assoc, this]; ring
  rw [hR, Finset.sum_comm (f := fun a b => if b < a ∧ ε b = ε a then μ a else 0)]
  have hL : ∀ a b, (if ε a = ε b then (if a = b then μ a ^ 2 else if a < b then μ a - μ b else 0)
      else 0 : ℝ) = (if a = b then μ a ^ 2 else 0) + (if a < b ∧ ε b = ε a then μ a else 0)
        - (if a < b ∧ ε a = ε b then μ b else 0) := by
    intro a b
    rcases lt_trichotomy a b with h2 | rfl | h2
    · by_cases h1 : ε a = ε b
      · simp [h1, h2, h2.ne]
      · have h1' : ¬ ε b = ε a := fun h => h1 h.symm
        simp [h1, h1', h2.ne]
    · simp
    · simp [h2.ne', not_lt.mpr h2.le]
  simp only [hL, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

theorem compact_casimir_highest_weight (h : KRel ε F) {μ : Fin n → ℝ} {x : V} (hx : KHighest ε F μ x) :
    CasK ε F x = ((ckv ε μ : ℝ) : ℂ) • x := by
  rw [compact_casimir_apply, ← compact_casimir_value_eq μ]
  have : ∀ a b, (if ε a = ε b then F a b (F b a x) else 0) =
      (((if ε a = ε b then (if a = b then μ a ^ 2 else if a < b then μ a - μ b else 0) else 0 : ℝ))
        : ℂ) • x := by
    intro a b
    by_cases hab : ε a = ε b
    · rw [if_pos hab, if_pos hab, compact_casimir_term_highest h hx hab]
    · simp [hab]
  simp_rw [this, ← Finset.sum_smul]
  push_cast
  rfl
end cas

theorem compact_casimir_span_holds : KCasSpan := by
  intro V _ _ n ε F μ x h hx y hy
  have hS : kSpan ε F x ≤ (CasK ε F).eigenspace ((ckv ε μ : ℝ) : ℂ) := by
    apply compact_span_le_stable
    · rw [Module.End.mem_eigenspace_iff]; exact compact_casimir_highest_weight h hx
    · intro a b hab z hz
      rw [Module.End.mem_eigenspace_iff] at hz ⊢
      have := LinearMap.congr_fun (compact_lie_commute_casimir h hab) z
      simp only [Module.End.mul_apply] at this
      rw [← this, hz, map_smul]
  exact Module.End.mem_eigenspace_iff.mp (hS hy)

end Formalism.REAL
