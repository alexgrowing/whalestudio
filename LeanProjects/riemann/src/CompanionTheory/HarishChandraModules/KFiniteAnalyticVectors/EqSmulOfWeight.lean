import Formalism.HermitianCurvature.CapelliDeterminantAndBranching

open Formalism.REAL Formalism.FourierDecayAlt.Qr

noncomputable section

namespace CompanionTheory.D.gk.HwAlg

variable {U : Type} [AddCommGroup U] [Module ℂ U] {n : ℕ}

def Lower (l : List (Fin n × Fin n)) : Prop := ∀ p ∈ l, p.2 < p.1

def word (F : Fin n → Fin n → Module.End ℂ U) (l : List (Fin n × Fin n)) : Module.End ℂ U :=
  (l.map fun p => F p.1 p.2).prod

@[simp] lemma word_nil (F : Fin n → Fin n → Module.End ℂ U) : word F [] = 1 := rfl

@[simp] lemma word_cons (F : Fin n → Fin n → Module.End ℂ U) (p : Fin n × Fin n) (l : List (Fin n × Fin n)) :
    word F (p :: l) = F p.1 p.2 * word F l := by
  simp [word]

def lowSpan (F : Fin n → Fin n → Module.End ℂ U) (w : U) : Submodule ℂ U :=
  Submodule.span ℂ {x | ∃ l, Lower l ∧ x = word F l w}

lemma word_mem (F : Fin n → Fin n → Module.End ℂ U) (w : U) {l : List (Fin n × Fin n)} (hl : Lower l) :
    word F l w ∈ lowSpan F w :=
  Submodule.subset_span ⟨l, hl, rfl⟩

lemma self_mem (F : Fin n → Fin n → Module.End ℂ U) (w : U) : w ∈ lowSpan F w := by
  simpa using word_mem F w (l := []) (by simp [Lower])

lemma lower_mem (F : Fin n → Fin n → Module.End ℂ U) (w : U) {a b : Fin n} (hab : b < a) {x : U}
    (hx : x ∈ lowSpan F w) : F a b x ∈ lowSpan F w := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    have : F a b (word F l w) = word F ((a, b) :: l) w := by simp
    rw [this]
    refine word_mem F w ?_
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact hab
    · exact hl p hp
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

lemma comm_apply {F : Fin n → Fin n → Module.End ℂ U} (hF : GlRel F) (i j a b : Fin n) (u : U) :
    F i j (F a b u) = F a b (F i j u) +
      ((if j = a then F i b u else 0) - (if b = i then F a j u else 0)) := by
  have h := congrArg (fun T : Module.End ℂ U => T u) (hF i j a b)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  split_ifs at h ⊢ <;> simp_all [sub_eq_iff_eq_add, add_comm]

variable {F : Fin n → Fin n → Module.End ℂ U} {ν : Fin n → ℂ} {w : U}

lemma gen_mem (hF : GlRel F) (hw : IsHW F ν w) :
    ∀ (l : List (Fin n × Fin n)), Lower l → ∀ i j, F i j (word F l w) ∈ lowSpan F w := by
  intro l
  induction l with
  | nil =>
    intro _ i j
    simp only [word_nil, Module.End.one_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · rw [hw.2 i j h]; exact Submodule.zero_mem _
    · rw [hw.1 i]; exact Submodule.smul_mem _ _ (self_mem F w)
    · exact lower_mem F w h (self_mem F w)
  | cons p l ih =>
    intro hl i j
    have hl' : Lower l := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hp : p.2 < p.1 := hl p (by simp)
    rw [word_cons, Module.End.mul_apply, comm_apply hF]
    refine Submodule.add_mem _ (lower_mem F w hp (ih hl' i j)) (Submodule.sub_mem _ ?_ ?_)
    · split_ifs
      · exact ih hl' _ _
      · exact Submodule.zero_mem _
    · split_ifs
      · exact ih hl' _ _
      · exact Submodule.zero_mem _

theorem stab_lowSpan (hF : GlRel F) (hw : IsHW F ν w) : Stab F (lowSpan F w) := by
  intro i j x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact gen_mem hF hw l hl i j
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

def wt (ν : Fin n → ℂ) : List (Fin n × Fin n) → Fin n → ℂ
  | [] => ν
  | p :: l => wt ν l + (Pi.single p.1 1 - Pi.single p.2 1)

lemma diag_word (hF : GlRel F) (hw : IsHW F ν w) :
    ∀ (l : List (Fin n × Fin n)) (c : Fin n), F c c (word F l w) = wt ν l c • word F l w := by
  intro l
  induction l with
  | nil => intro c; simpa [wt] using hw.1 c
  | cons p l ih =>
    intro c
    rw [word_cons, Module.End.mul_apply, comm_apply hF, ih, map_smul]
    simp only [wt, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
    by_cases h1 : c = p.1 <;> by_cases h2 : p.2 = c
    · subst h1; rw [h2] at *; simp
    · subst h1; simp [h2, Ne.symm h2, add_smul]
    · subst h2; simp [h1, add_smul, sub_eq_add_neg]
    · simp [h1, h2, Ne.symm h2]

def hgt (μ : Fin n → ℂ) : ℂ := ∑ c : Fin n, ((n : ℂ) - ((c : ℕ) : ℂ)) * μ c

lemma hgt_wt_re (ν : Fin n → ℂ) :
    ∀ l : List (Fin n × Fin n), Lower l → (hgt (wt ν l)).re ≤ (hgt ν).re - l.length := by
  intro l
  induction l with
  | nil => intro; simp [wt]
  | cons p l ih =>
    intro hl
    have hl' : Lower l := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hp : p.2 < p.1 := hl p (by simp)
    have hsum : hgt (wt ν (p :: l)) = hgt (wt ν l) + (((p.2 : ℕ) : ℂ) - ((p.1 : ℕ) : ℂ)) := by
      simp only [hgt, wt, Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      ring
    rw [hsum, Complex.add_re, Complex.sub_re, Complex.natCast_re, Complex.natCast_re]
    have : ((p.2 : ℕ) : ℝ) + 1 ≤ ((p.1 : ℕ) : ℝ) := by exact_mod_cast hp
    have := ih hl'
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

def hOp (F : Fin n → Fin n → Module.End ℂ U) : Module.End ℂ U :=
  ∑ c : Fin n, ((n : ℂ) - ((c : ℕ) : ℂ)) • F c c

lemma hOp_of_diag {x : U} {μ : Fin n → ℂ} (hx : ∀ c, F c c x = μ c • x) : hOp F x = hgt μ • x := by
  simp only [hOp, LinearMap.sum_apply, LinearMap.smul_apply, hx, smul_smul, hgt, Finset.sum_smul]

theorem eq_smul_of_weight (hF : GlRel F) (hw : IsHW F ν w) {x : U} (hx : x ∈ lowSpan F w)
    (hxν : ∀ c, F c c x = ν c • x) : ∃ t : ℂ, x = t • w := by
  set S1 : Set U := {y | ∃ l, Lower l ∧ l ≠ [] ∧ y = word F l w} with hS1
  have hset : {y | ∃ l, Lower l ∧ y = word F l w} = insert w S1 := by
    ext y; constructor
    · rintro ⟨l, hl, rfl⟩
      rcases l with _ | ⟨p, l⟩
      · left; simp
      · right; exact ⟨p :: l, hl, by simp, rfl⟩
    · rintro (rfl | ⟨l, hl, -, rfl⟩)
      · exact ⟨[], by simp [Lower], by simp⟩
      · exact ⟨l, hl, rfl⟩
  rw [lowSpan, hset, Submodule.mem_span_insert] at hx
  obtain ⟨t, y, hy, rfl⟩ := hx
  refine ⟨t, ?_⟩
  suffices y = 0 by rw [this, add_zero]

  have hy1 : y ∈ ⨆ (μ : ℂ) (_ : μ ≠ hgt ν), (hOp F).eigenspace μ := by
    refine (Submodule.span_le.2 ?_) hy
    rintro z ⟨l, hl, hne, rfl⟩
    have hre := hgt_wt_re ν l hl
    have hlen : (1 : ℝ) ≤ l.length := by
      rcases l with _ | ⟨p, l⟩
      · exact absurd rfl hne
      · simp
    have hne' : hgt (wt ν l) ≠ hgt ν := by
      intro h; rw [h] at hre; linarith
    refine Submodule.mem_iSup_of_mem (hgt (wt ν l)) (Submodule.mem_iSup_of_mem hne' ?_)
    rw [Module.End.mem_eigenspace_iff]
    exact hOp_of_diag (diag_word hF hw l)

  have hy2 : y ∈ (hOp F).eigenspace (hgt ν) := by
    rw [Module.End.mem_eigenspace_iff]
    have h1 : hOp F (t • w + y) = hgt ν • (t • w + y) := hOp_of_diag hxν
    have h2 : hOp F w = hgt ν • w := hOp_of_diag hw.1
    rw [map_add, map_smul, h2, smul_add, smul_comm] at h1
    exact add_left_cancel h1
  have hdisj := (Module.End.eigenspaces_iSupIndep (hOp F)) (hgt ν)
  exact (Submodule.disjoint_def.1 hdisj) y hy2 hy1

end CompanionTheory.D.gk.HwAlg
