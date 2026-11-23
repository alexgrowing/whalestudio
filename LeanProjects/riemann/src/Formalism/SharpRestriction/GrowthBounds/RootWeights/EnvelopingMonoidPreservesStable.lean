import Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicProjectorFixedMem

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem mem_weightSpace_iff_diag_action (E : GLOps n K V) (mu : Fin n → ℤ) (x : V) :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  simp [weightSp, Submodule.mem_iInf, sub_eq_zero]

theorem gl_operator_commutator {E : GLOps n K V}
    (hrel : ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0))
    (a b c d : Fin n) (x : V) :
    E a b (E c d x) = E c d (E a b x) + ((if b = c then E a d x else 0) - (if d = a then E c b x else 0)) := by
  have hx : E a b (E c d x) - E c d (E a b x) = (if b = c then E a d x else 0) - (if d = a then E c b x else 0) := by
    have h1 := LinearMap.congr_fun (hrel a b c d) x
    split_ifs at h1 ⊢ <;> simpa using h1
  rw [← hx]
  abel

theorem operator_shifts_weight_by_root {E : GLOps n K V}
    (hrel : ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0))
    (a b : Fin n) (mu : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E mu) :
    E a b x ∈ weightSp E (mu + rootW a b) := by
  rw [mem_weightSpace_iff_diag_action] at hx ⊢
  intro c
  rw [gl_operator_commutator hrel c c a b x, hx c, map_smul]
  by_cases hca : c = a <;> by_cases hcb : c = b
  · subst hca; subst hcb; simp [rootW]
  · subst hca; simp [rootW, Pi.single_apply, hcb, Ne.symm hcb, add_smul]
  · subst hcb; simp [rootW, Pi.single_apply, hca, sub_smul, add_smul]
  · simp [rootW, Pi.single_apply, hca, hcb, Ne.symm hcb]

inductive LoweringWordAlt (E : GLOps n K V) (h : V) : ℕ → V → Prop
  | zero : LoweringWordAlt E h 0 h
  | succ {k : ℕ} {x : V} {a b : Fin n} : b < a → LoweringWordAlt E h k x → LoweringWordAlt E h (k + 1) (E a b x)

def loweringSpan (E : GLOps n K V) (h : V) : Submodule K V := Submodule.span K {x | ∃ k, LoweringWordAlt E h k x}

private theorem c14D_Low_mem_lemma {E : GLOps n K V} {h : V} {k : ℕ} {x : V}
    (hx : LoweringWordAlt E h k x) : x ∈ loweringSpan E h := by
  unfold loweringSpan
  exact Submodule.subset_span ⟨k, hx⟩

theorem lowering_span_stable_lowering (E : GLOps n K V) (h : V) {a b : Fin n} (hab : b < a) (z : V) (hz : z ∈ loweringSpan E h) :
    E a b z ∈ loweringSpan E h := by
  have key : loweringSpan E h ≤ (loweringSpan E h).comap (E a b) := by
    refine Submodule.span_le.mpr ?_
    rintro y ⟨k, hk⟩
    exact Submodule.mem_comap.mpr (c14D_Low_mem_lemma (LoweringWordAlt.succ hab hk))
  exact key hz

theorem mem_highestWeight_iff (E : GLOps n K V) (lam : Fin n → ℤ) (h : V) :
    h ∈ highestWeightVectors E lam ↔ h ∈ weightSp E lam ∧ ∀ a b, a < b → E a b h = 0 := by
  simp only [highestWeightVectors, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]

theorem lowering_word_operator_mem_span {E : GLOps n K V}
    (hrel : ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0))
    (lam : Fin n → ℤ) (h : V) (hh : h ∈ highestWeightVectors E lam) (k : ℕ) (x : V) (hx : LoweringWordAlt E h k x) :
    ∀ c d, E c d x ∈ loweringSpan E h := by
  induction hx with
  | zero =>
    intro c d
    have hh' := (mem_highestWeight_iff E lam h).1 hh
    rcases lt_trichotomy c d with hcd | hcd | hcd
    · rw [hh'.2 c d hcd]
      exact Submodule.zero_mem _
    · subst hcd
      rw [(mem_weightSpace_iff_diag_action E lam h).1 hh'.1 c]
      exact Submodule.smul_mem _ _ (c14D_Low_mem_lemma LoweringWordAlt.zero)
    · exact c14D_Low_mem_lemma (LoweringWordAlt.succ hcd LoweringWordAlt.zero)
  | @succ k y a b hab hk ih =>
    intro c d
    rw [gl_operator_commutator hrel c d a b y]
    refine Submodule.add_mem _ (lowering_span_stable_lowering E h hab _ (ih c d)) (Submodule.sub_mem _ ?_ ?_)
    · split_ifs
      · exact ih c b
      · exact Submodule.zero_mem _
    · split_ifs
      · exact ih a d
      · exact Submodule.zero_mem _

theorem lowering_span_stable_all {E : GLOps n K V}
    (hrel : ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0))
    (lam : Fin n → ℤ) (h : V) (hh : h ∈ highestWeightVectors E lam) (c d : Fin n) (z : V) (hz : z ∈ loweringSpan E h) :
    E c d z ∈ loweringSpan E h := by
  have key : loweringSpan E h ≤ (loweringSpan E h).comap (E c d) := by
    refine Submodule.span_le.mpr ?_
    rintro y ⟨k, hk⟩
    exact Submodule.mem_comap.mpr (lowering_word_operator_mem_span hrel lam h hh k y hk c d)
  exact key hz

theorem enveloping_monoid_preserves_stable (E : GLOps n K V) (W : Submodule K V) (hW : ∀ a b, ∀ z ∈ W, E a b z ∈ W)
    (u : Module.End K V) (hu : u ∈ Umon E) : ∀ z ∈ W, u z ∈ W := by
  let S : Submonoid (Module.End K V) :=
    { carrier := {f | ∀ z ∈ W, f z ∈ W}
      mul_mem' := by
        intro f g hf hg
        show ∀ z ∈ W, (f * g) z ∈ W
        intro z hz
        exact hf _ (hg z hz)
      one_mem' := by
        show ∀ z ∈ W, (1 : Module.End K V) z ∈ W
        intro z hz
        exact hz }
  have hle : Umon E ≤ S := by
    unfold Umon
    rw [Submonoid.closure_le]
    rintro _ ⟨⟨a, b⟩, rfl⟩
    show ∀ z ∈ W, E a b z ∈ W
    exact hW a b
  exact hle hu

theorem generated_le_lowering_span {E : GLOps n K V}
    (hrel : ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0))
    (lam : Fin n → ℤ) (h : V) (hh : h ∈ highestWeightVectors E lam) : generatedSubrep E h ≤ loweringSpan E h := by
  refine Submodule.span_le.mpr ?_
  rintro y ⟨u, hu, rfl⟩
  exact enveloping_monoid_preserves_stable E (loweringSpan E h) (fun a b z hz => lowering_span_stable_all hrel lam h hh a b z hz) u hu h
    (c14D_Low_mem_lemma LoweringWordAlt.zero)

def weightHeightSum (mu : Fin n → ℤ) : ℤ := ∑ a : Fin n, (a.val : ℤ) * mu a

theorem heightSum_add_root (mu : Fin n → ℤ) (a b : Fin n) :
    weightHeightSum (mu + rootW a b) = weightHeightSum mu + ((a.val : ℤ) - (b.val : ℤ)) := by
  simp only [weightHeightSum, Pi.add_apply, rootW, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  simp [Pi.single_apply]

theorem lowering_word_weight_and_monoid {E : GLOps n K V}
    (hrel : ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0))
    (lam : Fin n → ℤ) (h : V) (hh : h ∈ weightSp E lam) (k : ℕ) (x : V) (hx : LoweringWordAlt E h k x) :
    (∃ mu, x ∈ weightSp E mu ∧ weightHeightSum lam + k ≤ weightHeightSum mu) ∧ (∃ u ∈ Umon E, x = u h) ∧ (k = 0 → x = h) := by
  induction hx with
  | zero =>
    refine ⟨⟨lam, hh, by simp⟩, ⟨1, one_mem _, rfl⟩, fun _ => rfl⟩
  | @succ k y a b hab hk ih =>
    obtain ⟨⟨mu, hmu, hht⟩, ⟨u, hu, hyu⟩, -⟩ := ih
    have hE : E a b ∈ Umon E := by
      unfold Umon
      exact Submonoid.subset_closure ⟨(a, b), rfl⟩
    refine ⟨⟨mu + rootW a b, operator_shifts_weight_by_root hrel a b mu y hmu, ?_⟩, ⟨E a b * u, mul_mem hE hu, ?_⟩,
      fun h0 => absurd h0 (Nat.succ_ne_zero k)⟩
    · rw [heightSum_add_root]
      have hab' : b.val < a.val := hab
      push_cast
      omega
    · subst hyu
      rfl

end

theorem hwv_generated_multiple_of_hwv : GeneratedMultipleOfHWV := by
  intro K V _ _ _ n E hE lam h hh
  have hrel := hE.1
  refine le_trans (generated_le_lowering_span hrel lam h hh) ?_
  refine Submodule.span_le.mpr ?_
  rintro x ⟨k, hk⟩
  rw [SetLike.mem_coe]
  obtain ⟨⟨mu, hmu, hht⟩, ⟨u, hu, hxu⟩, h0⟩ :=
    lowering_word_weight_and_monoid hrel lam h ((mem_highestWeight_iff E lam h).1 hh).1 k x hk
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rw [h0 hk0]
    exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self h)
  · apply Submodule.mem_sup_right
    have hne : mu ≠ lam := by
      rintro rfl
      omega
    have hg : x ∈ generatedSubrep E h := by
      unfold generatedSubrep
      exact Submodule.subset_span ⟨u, hu, hxu⟩
    have hx : x ∈ weightSp E mu ⊓ generatedSubrep E h := Submodule.mem_inf.mpr ⟨hmu, hg⟩
    exact Submodule.mem_iSup_of_mem mu
      (Submodule.mem_iSup_of_mem (show mu ∈ {mu : Fin n → ℤ | mu ≠ lam} from hne) hx)

end Formalism.MainNotions.G.GLWeightTheory
