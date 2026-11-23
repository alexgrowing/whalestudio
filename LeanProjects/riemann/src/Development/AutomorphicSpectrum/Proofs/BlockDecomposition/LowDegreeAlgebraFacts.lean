import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.GlLowest

open PositivityTheory.RgDs PositivityTheory.RgDs.K ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
  {L : Fin n → Fin n → Module.End ℂ M} {Φ : M}

def IsRaising (r : List (Fin n × Fin n)) : Prop := ∀ p ∈ r, p.1 < p.2

def raiseSpan (L : Fin n → Fin n → Module.End ℂ M) (Φ : M) : Submodule ℂ M :=
  Submodule.span ℂ {x | ∃ r, IsRaising r ∧ x = lword L r Φ}

def wt (r : List (Fin n × Fin n)) : Fin n → ℝ := (r.map fun p => Formalism.REAL.root p.1 p.2).sum

theorem wt_cons (p : Fin n × Fin n) (r : List (Fin n × Fin n)) :
    wt (p :: r) = Formalism.REAL.root p.1 p.2 + wt r := by
  simp [wt]

theorem root_apply (a b c : Fin n) :
    Formalism.REAL.root a b c = (if c = a then 1 else 0) - (if c = b then 1 else 0) := by
  simp [Formalism.REAL.root, Pi.single_apply]

theorem lword_cons (p : Fin n × Fin n) (r : List (Fin n × Fin n)) (y : M) :
    lword L (p :: r) y = L p.1 p.2 (lword L r y) := rfl

theorem isRaising_nil : IsRaising ([] : List (Fin n × Fin n)) := fun _ h => by simp at h

theorem isRaising_cons {p : Fin n × Fin n} {r : List (Fin n × Fin n)} (hp : p.1 < p.2)
    (hr : IsRaising r) : IsRaising (p :: r) := by
  intro q hq
  rcases List.mem_cons.mp hq with h | h
  · subst h; exact hp
  · exact hr q h

theorem word_mem {r : List (Fin n × Fin n)} (hr : IsRaising r) : lword L r Φ ∈ raiseSpan L Φ :=
  Submodule.subset_span ⟨r, hr, rfl⟩

theorem phi_mem : Φ ∈ raiseSpan L Φ := word_mem (L := L) (Φ := Φ) isRaising_nil

theorem raise_stable {a b : Fin n} (h : a < b) : ∀ x ∈ raiseSpan L Φ, L a b x ∈ raiseSpan L Φ := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨r, hr, rfl⟩ := hy
    exact word_mem (r := (a, b) :: r) (isRaising_cons h hr)
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy

theorem gl_apply (hL : IsGlRep L) (a b c d : Fin n) (y : M) :
    L a b (L c d y) = L c d (L a b y) +
      ((if b = c then L a d y else 0) - (if d = a then L c b y else 0)) := by
  have h := congrArg (fun f : Module.End ℂ M => f y) (hL a b c d)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [← sub_eq_iff_eq_add', h]
  split_ifs <;> simp

theorem letter_word_mem (hL : IsGlRep L) {μ : Fin n → ℝ} (hd : ∀ a, L a a Φ = (μ a : ℂ) • Φ)
    (hlow : ∀ a b, b < a → L a b Φ = 0) :
    ∀ r : List (Fin n × Fin n), IsRaising r → ∀ a b, L a b (lword L r Φ) ∈ raiseSpan L Φ := by
  intro r
  induction r with
  | nil =>
    intro _ a b
    have h1 : lword L ([] : List (Fin n × Fin n)) Φ = Φ := rfl
    rw [h1]
    rcases lt_trichotomy a b with h | h | h
    · exact word_mem (r := [(a, b)]) (isRaising_cons h isRaising_nil)
    · subst h
      rw [hd a]
      exact Submodule.smul_mem _ _ phi_mem
    · rw [hlow a b h]; exact Submodule.zero_mem _
  | cons p r ih =>
    intro hr a b
    have hr' : IsRaising r := fun q hq => hr q (List.mem_cons_of_mem _ hq)
    have hp : p.1 < p.2 := hr p List.mem_cons_self
    rw [lword_cons, gl_apply hL]
    refine Submodule.add_mem _ (raise_stable hp _ (ih hr' a b)) (Submodule.sub_mem _ ?_ ?_)
    · split_ifs
      · exact ih hr' a p.2
      · exact Submodule.zero_mem _
    · split_ifs
      · exact ih hr' p.1 b
      · exact Submodule.zero_mem _

theorem letter_stable (hL : IsGlRep L) {μ : Fin n → ℝ} (hd : ∀ a, L a a Φ = (μ a : ℂ) • Φ)
    (hlow : ∀ a b, b < a → L a b Φ = 0) (a b : Fin n) :
    ∀ x ∈ raiseSpan L Φ, L a b x ∈ raiseSpan L Φ := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨r, hr, rfl⟩ := hy
    exact letter_word_mem hL hd hlow r hr a b
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy

theorem any_word_mem (hL : IsGlRep L) {μ : Fin n → ℝ} (hd : ∀ a, L a a Φ = (μ a : ℂ) • Φ)
    (hlow : ∀ a b, b < a → L a b Φ = 0) (w : List (Fin n × Fin n)) :
    lword L w Φ ∈ raiseSpan L Φ := by
  induction w with
  | nil => exact phi_mem
  | cons p w ih => exact letter_stable hL hd hlow p.1 p.2 _ ih

theorem diag_word (hL : IsGlRep L) {μ : Fin n → ℝ} (hd : ∀ a, L a a Φ = (μ a : ℂ) • Φ) :
    ∀ r : List (Fin n × Fin n), IsRaising r → ∀ c,
      L c c (lword L r Φ) = (((μ + wt r) c : ℝ) : ℂ) • lword L r Φ := by
  intro r
  induction r with
  | nil =>
    intro _ c
    have h1 : lword L ([] : List (Fin n × Fin n)) Φ = Φ := rfl
    rw [h1, hd c]
    simp [wt]
  | cons p r ih =>
    intro hr c
    have hr' : IsRaising r := fun q hq => hr q (List.mem_cons_of_mem _ hq)
    have hp : p.1 < p.2 := hr p List.mem_cons_self
    rw [lword_cons, gl_apply hL, ih hr' c, map_smul, wt_cons]
    simp only [Pi.add_apply, root_apply]
    by_cases h1 : c = p.1
    · have h2 : p.2 ≠ c := by rw [h1]; exact hp.ne'
      have h2' : c ≠ p.2 := h2.symm
      simp only [if_pos h1, if_neg h2, if_neg h2']
      subst h1
      push_cast
      module
    · by_cases h2 : p.2 = c
      · have h2' : c = p.2 := h2.symm
        simp only [if_neg h1, if_pos h2, if_pos h2']
        subst h2
        push_cast
        module
      · have h2' : c ≠ p.2 := fun h => h2 h.symm
        simp only [if_neg h1, if_neg h2, if_neg h2']
        push_cast
        module

theorem inCone_add_wt (μ : Fin n → ℝ) :
    ∀ r : List (Fin n × Fin n), IsRaising r → InCone μ (μ + wt r) := by
  intro r
  induction r with
  | nil => intro _; simpa [wt] using inCone_refl μ
  | cons p r ih =>
    intro hr
    have hr' : IsRaising r := fun q hq => hr q (List.mem_cons_of_mem _ hq)
    have hp : p.1 < p.2 := hr p List.mem_cons_self
    obtain ⟨c, hc, he⟩ := ih hr'
    refine ⟨fun a b => c a b + (if a = p.1 then (if b = p.2 then 1 else 0) else 0), ?_, ?_⟩
    · intro a b hab
      have hab' : c a b + (if a = p.1 then (if b = p.2 then 1 else 0) else 0) ≠ 0 := hab
      by_cases h0 : c a b = 0
      · by_cases h1 : a = p.1
        · by_cases h2 : b = p.2
          · rw [h1, h2]; exact hp
          · rw [h0, if_pos h1, if_neg h2] at hab'
            exact absurd rfl hab'
        · rw [h0, if_neg h1] at hab'
          exact absurd rfl hab'
      · exact hc a b h0
    · have hs : ∑ a, ∑ b, (((if a = p.1 then (if b = p.2 then 1 else 0) else 0 : ℕ) : ℝ)) •
          Formalism.REAL.root a b = Formalism.REAL.root p.1 p.2 := by
        rw [Finset.sum_eq_single p.1, Finset.sum_eq_single p.2]
        · simp
        · intro b _ hb; simp [hb]
        · simp
        · intro a _ ha; simp [ha]
        · simp
      have he' : wt r = ∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b := add_left_cancel he
      simp only [Nat.cast_add, add_smul, Finset.sum_add_distrib]
      rw [hs, ← he', wt_cons, add_comm (wt r)]

theorem pair_wt : ∀ r : List (Fin n × Fin n), IsRaising r →
    ∑ i : Fin n, (i : ℝ) * wt r i ≤ -(r.length : ℝ) := by
  intro r
  induction r with
  | nil => intro _; simp [wt]
  | cons p r ih =>
    intro hr
    have hr' : IsRaising r := fun q hq => hr q (List.mem_cons_of_mem _ hq)
    have hp : p.1 < p.2 := hr p List.mem_cons_self
    have h1 : ∑ i : Fin n, (i : ℝ) * Formalism.REAL.root p.1 p.2 i = (p.1 : ℝ) - (p.2 : ℝ) := by
      simp [root_apply, mul_sub, Finset.sum_sub_distrib]
    have h2 : ((p.1 : ℕ) : ℝ) + 1 ≤ ((p.2 : ℕ) : ℝ) := by
      exact_mod_cast hp
    have h3 := ih hr'
    rw [wt_cons]
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, List.length_cons, h1]
    push_cast
    linarith

theorem eq_nil_of_wt_eq_zero {r : List (Fin n × Fin n)} (hr : IsRaising r) (h : wt r = 0) : r = [] := by
  have h1 := pair_wt r hr
  rw [h] at h1
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h1
  have h2 : (r.length : ℝ) ≤ 0 := by linarith
  have h3 : r.length = 0 := by exact_mod_cast Nat.le_zero.mp (by exact_mod_cast h2)
  exact List.length_eq_zero_iff.mp h3

theorem eig_mem (f : Module.End ℂ M) (c : ℂ) (v : M) (h : f v = c • v) : v ∈ f.maxGenEigenspace c :=
  (Module.End.mem_maxGenEigenspace f c v).2 ⟨1, by simp [h]⟩

theorem diag_commute (hL : IsGlRep L) (i j : Fin n) : Commute (L i i) (L j j) := by
  by_cases h : i = j
  · subst h; exact Commute.refl _
  · have h1 := hL i i j j
    have h' : j ≠ i := fun e => h e.symm
    simp only [if_neg h, if_neg h', sub_self] at h1
    exact sub_eq_zero.mp h1

theorem mem_span_of_weight (hL : IsGlRep L) {μ η : Fin n → ℝ} (hd : ∀ a, L a a Φ = (μ a : ℂ) • Φ)
    {x : M} (hx : x ∈ raiseSpan L Φ) (hη : ∀ c, L c c x = (η c : ℂ) • x) :
    x ∈ Submodule.span ℂ {y | ∃ r, IsRaising r ∧ μ + wt r = η ∧ y = lword L r Φ} := by
  classical
  set S₁ : Set M := {y | ∃ r, IsRaising r ∧ μ + wt r = η ∧ y = lword L r Φ} with hS₁
  set S₂ : Set M := {y | ∃ r, IsRaising r ∧ μ + wt r ≠ η ∧ y = lword L r Φ} with hS₂
  let Wt : (Fin n → ℂ) → Submodule ℂ M := fun χ => ⨅ i, (L i i).maxGenEigenspace (χ i)
  have hind : iSupIndep Wt :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun i => L i i)
      (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (diag_commute hL j i) φ)
  let χη : Fin n → ℂ := fun c => (η c : ℂ)
  have hmemW : ∀ (χ : Fin n → ℂ) (v : M), (∀ c, L c c v = χ c • v) → v ∈ Wt χ := by
    intro χ v hv
    exact Submodule.mem_iInf _ |>.2 fun i => eig_mem _ _ _ (hv i)
  have hsup : raiseSpan L Φ ≤ Submodule.span ℂ S₁ ⊔ Submodule.span ℂ S₂ := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨r, hr, rfl⟩
    by_cases h : μ + wt r = η
    · exact (le_sup_left : Submodule.span ℂ S₁ ≤ _) (Submodule.subset_span ⟨r, hr, h, rfl⟩)
    · exact (le_sup_right : Submodule.span ℂ S₂ ≤ _) (Submodule.subset_span ⟨r, hr, h, rfl⟩)
  have h1 : Submodule.span ℂ S₁ ≤ Wt χη := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨r, hr, he, rfl⟩
    refine hmemW _ _ fun c => ?_
    rw [diag_word hL hd r hr c, he]
  have h2 : Submodule.span ℂ S₂ ≤ ⨆ (χ) (_ : χ ≠ χη), Wt χ := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨r, hr, he, rfl⟩
    have hne : (fun c => (((μ + wt r) c : ℝ) : ℂ)) ≠ χη := by
      intro h
      apply he
      funext c
      exact Complex.ofReal_injective (congrFun h c)
    have hm := hmemW _ _ (diag_word hL hd r hr)
    exact (le_iSup₂ (f := fun (χ : Fin n → ℂ) (_ : χ ≠ χη) => Wt χ) _ hne) hm
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hsup hx)
  have hxW : a + b ∈ Wt χη := hmemW _ _ hη
  have hbW : b ∈ Wt χη := by
    have := Submodule.sub_mem _ hxW (h1 ha)
    simpa using this
  have hb0 : b = 0 := Submodule.disjoint_def.1 (hind χη) b hbW (h2 hb)
  rw [hb0, add_zero]
  exact ha

theorem lowAlg : LowAlg := by
  intro n M _ _ L μ η Φ x hL hd hlow hx hη h0
  have hle : Submodule.span ℂ (Set.range fun w : List (Fin n × Fin n) => lword L w Φ) ≤ raiseSpan L Φ := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨w, rfl⟩
    exact any_word_mem hL hd hlow w
  have hx1 := mem_span_of_weight hL hd (hle hx) hη
  constructor
  · have hne : ({y | ∃ r, IsRaising r ∧ μ + wt r = η ∧ y = lword L r Φ} : Set M).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      rw [hemp, Submodule.span_empty, Submodule.mem_bot] at hx1
      exact h0 hx1
    obtain ⟨y, r, hr, he, -⟩ := hne
    rw [← he]
    exact inCone_add_wt μ r hr
  · intro hμ
    have hsub : Submodule.span ℂ {y | ∃ r, IsRaising r ∧ μ + wt r = η ∧ y = lword L r Φ} ≤
        Submodule.span ℂ {Φ} := by
      refine Submodule.span_le.2 ?_
      rintro y ⟨r, hr, he, rfl⟩
      have hw : wt r = 0 := by
        rw [hμ] at he
        exact add_eq_left.mp he
      have hnil := eq_nil_of_wt_eq_zero hr hw
      subst hnil
      exact Submodule.subset_span rfl
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hsub hx1)
    exact ⟨c, hc.symm⟩

end GlobalTheory.CompanionTheory.GlLowest
