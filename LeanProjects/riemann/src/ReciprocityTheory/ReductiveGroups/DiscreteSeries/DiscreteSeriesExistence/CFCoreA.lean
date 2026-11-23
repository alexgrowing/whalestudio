import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Straight

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}

def IsKLow (ε : Fin n → Bool) (p : Fin n × Fin n) : Prop := p.2 < p.1 ∧ ε p.1 = ε p.2

def lowWord (E : Fin n → Fin n → Module.End ℂ M) (y : M) : List (Fin n × Fin n) → M
  | [] => y
  | p :: l => E p.1 p.2 (lowWord E y l)

def lowWt (μ : Fin n → ℝ) : List (Fin n × Fin n) → Fin n → ℝ
  | [] => μ
  | p :: l => lowWt μ l + root p.1 p.2

def kLowSpan (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (y : M) : Submodule ℂ M :=
  Submodule.span ℂ {x | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, IsKLow ε p) ∧ x = lowWord E y l}

theorem lowWord_mem {y : M} {l : List (Fin n × Fin n)} (hl : ∀ p ∈ l, IsKLow ε p) :
    lowWord E y l ∈ kLowSpan ε E y := by
  unfold kLowSpan
  exact Submodule.subset_span ⟨l, hl, rfl⟩

theorem self_mem_kLowSpan (y : M) : y ∈ kLowSpan ε E y := by
  exact lowWord_mem (ε := ε) (E := E) (y := y) (l := []) (fun p hp => by simp at hp)

theorem lowWord_wt (hE : IsGlRep E) {μ : Fin n → ℝ} {y : M} (hy : ∀ a, E a a y = (μ a : ℂ) • y) :
    ∀ (l : List (Fin n × Fin n)) (a : Fin n),
      E a a (lowWord E y l) = (lowWt μ l a : ℂ) • lowWord E y l
  | [], a => by simpa [lowWord, lowWt] using hy a
  | p :: l, a => by
    obtain ⟨c, d⟩ := p
    have h := congrArg (fun X : Module.End ℂ M => X (lowWord E y l)) (hE a a c d)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [lowWord_wt hE hy l a, map_smul, sub_eq_iff_eq_add] at h
    simp only [lowWord, lowWt]
    rw [h]
    simp only [root, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
    by_cases hac : a = c <;> by_cases had : a = d
    · subst hac; subst had; simp
    · subst hac
      simp only [if_neg had, if_neg (Ne.symm had), LinearMap.zero_apply, sub_zero]
      push_cast
      module
    · subst had
      simp only [if_neg hac, LinearMap.zero_apply, zero_sub]
      push_cast
      module
    · simp [hac, had, Ne.symm had]

private lemma mem_kLowSpan_of_map_lowWord_mem {y : M} (T : Module.End ℂ M)
    (h : ∀ l : List (Fin n × Fin n), (∀ p ∈ l, IsKLow ε p) → T (lowWord E y l) ∈ kLowSpan ε E y) :
    ∀ x ∈ kLowSpan ε E y, T x ∈ kLowSpan ε E y := by
  intro x hx
  have hle : kLowSpan ε E y ≤ (kLowSpan ε E y).comap T := by
    unfold kLowSpan
    rw [Submodule.span_le]
    rintro _ ⟨l, hl, rfl⟩
    exact h l hl
  exact hle hx

theorem kLowSpan_low_stable {y : M} {c d : Fin n} (hcd : IsKLow ε (c, d)) :
    ∀ x ∈ kLowSpan ε E y, E c d x ∈ kLowSpan ε E y := by
  exact mem_kLowSpan_of_map_lowWord_mem (E c d) (fun l hl => lowWord_mem (ε := ε) (E := E) (y := y) (l := (c, d) :: l) (by
    intro p hp
    rcases List.mem_cons.mp hp with h | h
    · rw [h]; exact hcd
    · exact hl p h))

theorem lowWord_mem_of_ge (hE : IsGlRep E) {μ : Fin n → ℝ} {y : M} (hy : ∀ a, E a a y = (μ a : ℂ) • y)
    {l : List (Fin n × Fin n)} (hl : ∀ p ∈ l, IsKLow ε p) {a b : Fin n} (hab : b ≤ a) (hε : ε a = ε b) :
    E a b (lowWord E y l) ∈ kLowSpan ε E y := by
  rcases hab.lt_or_eq with h | h
  · exact lowWord_mem (ε := ε) (E := E) (y := y) (l := (a, b) :: l) (by
      intro p hp
      rcases List.mem_cons.mp hp with hp | hp
      · rw [hp]; exact And.intro h hε
      · exact hl p hp)
  · rw [h, lowWord_wt hE hy l a]
    exact Submodule.smul_mem _ _ (lowWord_mem hl)

theorem lowWord_raise (hE : IsGlRep E) {μ : Fin n → ℝ} {y : M} (hy : IsKHWVec ε E μ y) :
    ∀ (l : List (Fin n × Fin n)), (∀ p ∈ l, IsKLow ε p) → ∀ a b : Fin n, a < b → ε a = ε b →
      E a b (lowWord E y l) ∈ kLowSpan ε E y
  | [], _, a, b, hab, hε => by
    simp only [lowWord]
    rw [hy.2 a b hab hε]
    exact Submodule.zero_mem _
  | p :: l, hl, a, b, hab, hε => by
    obtain ⟨c, d⟩ := p
    have hcd : IsKLow ε (c, d) := hl _ (List.mem_cons_self ..)
    have hl' : ∀ p ∈ l, IsKLow ε p := fun p hp => hl p (List.mem_cons_of_mem _ hp)
    have ih := lowWord_raise hE hy l hl'
    have key : ∀ a' b' : Fin n, ε a' = ε b' → E a' b' (lowWord E y l) ∈ kLowSpan ε E y := by
      intro a' b' h'
      rcases lt_or_ge a' b' with h | h
      · exact ih a' b' h h'
      · exact lowWord_mem_of_ge hE hy.1 hl' h h'
    have h := congrArg (fun X : Module.End ℂ M => X (lowWord E y l)) (hE a b c d)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [sub_eq_iff_eq_add] at h
    simp only [lowWord]
    rw [h]
    refine Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_) (kLowSpan_low_stable hcd _ (ih a b hab hε))
    · split_ifs with hbc
      · subst hbc; exact key a d (hε.trans hcd.2)
      · simp
    · split_ifs with hda
      · subst hda; exact key c b (hcd.2.trans hε)
      · simp

theorem kLowSpan_kStable (hE : IsGlRep E) {μ : Fin n → ℝ} {y : M} (hy : IsKHWVec ε E μ y) :
    IsKStableSub ε E (kLowSpan ε E y) := by
  have hy' : (∀ a, E a a y = (μ a : ℂ) • y) ∧ ∀ a b, a < b → ε a = ε b → E a b y = 0 := hy
  intro a b hab
  exact mem_kLowSpan_of_map_lowWord_mem (E a b) (fun l hl => by
    rcases lt_or_ge a b with h | h
    · exact lowWord_raise hE hy l hl a b h hab
    · exact lowWord_mem_of_ge hE hy'.1 hl h hab)

theorem kLowSpan_le {y : M} {T : Submodule ℂ M} (hT : IsKStableSub ε E T) (hy : y ∈ T) :
    kLowSpan ε E y ≤ T := by
  have hW : ∀ l : List (Fin n × Fin n), (∀ p ∈ l, IsKLow ε p) → lowWord E y l ∈ T := by
    intro l
    induction l with
    | nil => intro _; exact hy
    | cons p l ih =>
      intro hl
      have hp : p.2 < p.1 ∧ ε p.1 = ε p.2 := hl p (by simp)
      exact hT p.1 p.2 hp.2 _ (ih fun q hq => hl q (List.mem_cons_of_mem _ hq))
  unfold kLowSpan
  rw [Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  exact hW l hl

theorem lowWt_ht (μ : Fin n → ℝ) :
    ∀ l : List (Fin n × Fin n), (∀ p ∈ l, IsKLow ε p) →
      (∑ i : Fin n, ((i : ℕ) : ℝ) * μ i) + l.length ≤ ∑ i : Fin n, ((i : ℕ) : ℝ) * lowWt μ l i
  | [], _ => by simp [lowWt]
  | p :: l, hl => by
    have ih := lowWt_ht μ l fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hp := (hl p (List.mem_cons_self ..)).1
    have hr : ∑ i : Fin n, ((i : ℕ) : ℝ) * root p.1 p.2 i = (p.1 : ℝ) - (p.2 : ℝ) := by
      simp [root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
    have hlt : ((p.2 : ℕ) : ℝ) + 1 ≤ ((p.1 : ℕ) : ℝ) := by exact_mod_cast hp
    simp only [lowWt, Pi.add_apply, mul_add, Finset.sum_add_distrib, hr, List.length_cons]
    push_cast
    linarith

theorem lowWt_ne {μ : Fin n → ℝ} {l : List (Fin n × Fin n)} (hl : ∀ p ∈ l, IsKLow ε p) (hne : l ≠ []) :
    lowWt μ l ≠ μ := by
  intro h
  have h2 := lowWt_ht (ε := ε) μ l hl
  rw [h] at h2
  cases l with
  | nil => exact hne rfl
  | cons p l =>
    rw [List.length_cons, Nat.cast_add, Nat.cast_one] at h2
    have : (0 : ℝ) ≤ l.length := Nat.cast_nonneg _
    linarith

end Straight

section Unitary

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}

private lemma inner_eq_zero_of_distinct_weights (hU : IsInfUnitary ε E) {μ ν : Fin n → ℝ} {u v : M}
    (hu : ∀ a, E a a u = (μ a : ℂ) • u) (hv : ∀ a, E a a v = (ν a : ℂ) • v) (hne : ν ≠ μ) :
    inner ℂ u v = 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
  have h := hU a a u v
  have hs : adjSign ε a a = 1 := by simp [adjSign]
  rw [hu a, hv a, inner_smul_left, inner_smul_right, hs, one_mul, Complex.conj_ofReal] at h
  have h3 : ((μ a : ℂ) - (ν a : ℂ)) * inner ℂ u v = 0 := by rw [sub_mul, h, sub_self]
  have h5 : (μ a : ℂ) - (ν a : ℂ) ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast Ne.symm ha
  exact (mul_eq_zero.mp h3).resolve_left h5

theorem kLowSpan_line (hE : IsGlRep E) (hU : IsInfUnitary ε E) {μ : Fin n → ℝ} {y : M}
    (hy : IsKHWVec ε E μ y) (hy0 : y ≠ 0) {z : M} (hz : z ∈ kLowSpan ε E y)
    (hzw : ∀ a, E a a z = (μ a : ℂ) • z) : ∃ c : ℂ, z = c • y := by
  have hy' : (∀ a, E a a y = (μ a : ℂ) • y) ∧ ∀ a b, a < b → ε a = ε b → E a b y = 0 := hy
  obtain ⟨W, hW⟩ : ∃ W : Submodule ℂ M, W = Submodule.span ℂ
      {x | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, IsKLow ε p) ∧ l ≠ [] ∧ x = lowWord E y l} := ⟨_, rfl⟩
  have hle : kLowSpan ε E y ≤ Submodule.span ℂ {y} ⊔ W := by
    unfold kLowSpan
    rw [Submodule.span_le]
    rintro _ ⟨l, hl, rfl⟩
    rcases l with _ | ⟨p, l⟩
    · exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self y)
    · apply Submodule.mem_sup_right
      rw [hW]
      exact Submodule.subset_span ⟨p :: l, hl, List.cons_ne_nil _ _, rfl⟩
  have horth : ∀ u : M, (∀ a, E a a u = (μ a : ℂ) • u) → ∀ g ∈ W, inner ℂ u g = 0 := by
    intro u hu g hg
    have hWle : W ≤ (Submodule.span ℂ {u})ᗮ := by
      rw [hW, Submodule.span_le]
      rintro _ ⟨l, hl, hne, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
      exact inner_eq_zero_of_distinct_weights hU hu (lowWord_wt hE hy'.1 l) (lowWt_ne hl hne)
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hWle hg)
  obtain ⟨y', hy'', w, hw, hzw'⟩ := Submodule.mem_sup.mp (hle hz)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy''
  have h1 := horth z hzw w hw
  have h2 := horth y hy'.1 w hw
  have hww : inner ℂ w w = 0 := by
    calc inner ℂ w w = inner ℂ (z - c • y) w := by rw [← hzw', add_sub_cancel_left]
      _ = 0 := by rw [inner_sub_left, inner_smul_left, h1, h2, mul_zero, sub_zero]
  have hw0 : w = 0 := inner_self_eq_zero.mp hww
  exact ⟨c, by rw [← hzw', hw0, add_zero]⟩

theorem khw_line_of_kIrrHW (hE : IsGlRep E) (hU : IsInfUnitary ε E) {μ : Fin n → ℝ} {S : Submodule ℂ M}
    (hS : IsKIrrHW ε E μ S) {x y : M} (hx : x ∈ S) (hy : y ∈ S) (hxw : IsKHWVec ε E μ x)
    (hyw : IsKHWVec ε E μ y) (hy0 : y ≠ 0) : ∃ c : ℂ, x = c • y := by
  have hS' : FiniteDimensional ℂ S ∧ IsKStableSub ε E S ∧
      (∀ S' : Submodule ℂ M, S' ≤ S → IsKStableSub ε E S' → S' = ⊥ ∨ S' = S) ∧
      ∃ w ∈ S, w ≠ 0 ∧ IsKHWVec ε E μ w := hS
  obtain ⟨_, hSt, hirr, _⟩ := hS'
  have hx1 : (∀ a, E a a x = (μ a : ℂ) • x) ∧ ∀ a b, a < b → ε a = ε b → E a b x = 0 := hxw
  have hle : kLowSpan ε E y ≤ S := kLowSpan_le hSt hy
  have heq : kLowSpan ε E y = S := by
    rcases hirr _ hle (kLowSpan_kStable hE hyw) with h | h
    · exfalso
      apply hy0
      have hmem : y ∈ kLowSpan ε E y := self_mem_kLowSpan y
      rw [h] at hmem
      exact (Submodule.mem_bot ℂ).mp hmem
    · exact h
  exact kLowSpan_line hE hU hyw hy0 (by rw [heq]; exact hx) hx1.1

theorem kLowSpan_kIrrHW (hE : IsGlRep E) (hU : IsInfUnitary ε E) {μ : Fin n → ℝ} {y : M}
    (hy : IsKHWVec ε E μ y) (hy0 : y ≠ 0) (hfin : FiniteDimensional ℂ (kLowSpan ε E y)) :
    IsKIrrHW ε E μ (kLowSpan ε E y) := by
  have hy' : (∀ a, E a a y = (μ a : ℂ) • y) ∧ ∀ a b, a < b → ε a = ε b → E a b y = 0 := hy
  refine ⟨hfin, kLowSpan_kStable hE hy, ?_, y, self_mem_kLowSpan y, hy0, hy⟩
  intro S' hS'le hS'st
  haveI : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hS'le
  have hperp : IsKStableSub ε E S'ᗮ := by
    intro a b hab v hv
    rw [Submodule.mem_orthogonal]
    intro u hu
    have h := hU b a u v
    have hs : adjSign ε b a = 1 := by simp [adjSign, hab]
    rw [hs, one_mul] at h
    rw [← h]
    exact (Submodule.mem_orthogonal _ _).mp hv _ (hS'st b a hab.symm u hu)
  have hzero : ∀ x, x ∈ S' → x ∈ S'ᗮ → x = 0 := fun x h1 h2 =>
    inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal h1 h2)
  obtain ⟨y1, hy1, y2, hy2, hsum⟩ := S'.exists_add_mem_mem_orthogonal y
  have hy1w : ∀ a, E a a y1 = (μ a : ℂ) • y1 := by
    intro a
    have h := hy'.1 a
    rw [hsum, map_add, smul_add] at h
    have hm : E a a y1 - (μ a : ℂ) • y1 = (μ a : ℂ) • y2 - E a a y2 := by
      rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
    have h0 := hzero _ (sub_mem (hS'st a a rfl y1 hy1) (Submodule.smul_mem _ _ hy1))
      (by rw [hm]; exact sub_mem (Submodule.smul_mem _ _ hy2) (hperp a a rfl y2 hy2))
    exact sub_eq_zero.mp h0
  obtain ⟨c, hc⟩ := kLowSpan_line hE hU hy hy0 (hS'le hy1) hy1w
  by_cases hc0 : c = 0
  · left
    rw [hc0, zero_smul] at hc
    have hyperp : y ∈ S'ᗮ := by rw [hsum, hc, zero_add]; exact hy2
    have hle2 : kLowSpan ε E y ≤ S'ᗮ := kLowSpan_le hperp hyperp
    rw [Submodule.eq_bot_iff]
    intro x hx
    exact hzero x hx (hle2 (hS'le hx))
  · right
    have hyS : y ∈ S' := by
      have hyc : y = c⁻¹ • y1 := by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [hyc]
      exact Submodule.smul_mem _ _ hy1
    exact le_antisymm hS'le (kLowSpan_le hS'st hyS)

end Unitary

end ReciprocityTheory.ChartRestriction.DS
