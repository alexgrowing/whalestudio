import Formalism.SharpRestriction.GrowthBounds.RootWeights.NontrivialIsotypicWeightZeroKilled

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem mem_weightSpace_iff_diag_eigen {E : GLOps n K V} {mu : Fin n → ℤ} {x : V} :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  unfold weightSp
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  all_goals exact Iff.rfl

theorem weight_zero_lowering_kills_raising [CharZero K] [FiniteDimensional K V] {E : GLOps n K V} (hE : IsGLRep E) {v : V}
    (hv : v ∈ weightSp E 0) (a b : Fin n) (hab : a ≠ b) (he : E a b v = 0) : E b a v = 0 := by
  have hva : E a a v = 0 := by simpa using (mem_weightSpace_iff_diag_eigen.mp hv) a
  have hvb : E b b v = 0 := by simpa using (mem_weightSpace_iff_diag_eigen.mp hv) b
  have rAA : ∀ y, E a a (E b a y) = E b a (E a a y) - E b a y := by
    intro y
    have h := LinearMap.congr_fun (hE.1 a a b a) y
    rw [if_neg hab, if_pos rfl, LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.zero_apply,
      zero_sub] at h
    rw [sub_eq_add_neg]
    exact sub_eq_iff_eq_add'.mp h
  have rBB : ∀ y, E b b (E b a y) = E b a (E b b y) + E b a y := by
    intro y
    have h := LinearMap.congr_fun (hE.1 b b b a) y
    rw [if_pos rfl, if_neg hab, LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.zero_apply,
      sub_zero] at h
    exact sub_eq_iff_eq_add'.mp h
  have rEF : ∀ y, E a b (E b a y) = E b a (E a b y) + (E a a y - E b b y) := by
    intro y
    have h := LinearMap.congr_fun (hE.1 a b b a) y
    rw [if_pos rfl, if_pos rfl, LinearMap.sub_apply, LinearMap.sub_apply] at h
    exact sub_eq_iff_eq_add'.mp h
  have hstep : ∀ j : ℕ, E b a ((⇑(E b a))^[j] v) = (⇑(E b a))^[j+1] v :=
    fun j => (Function.iterate_succ_apply' _ j v).symm
  have hA : ∀ k : ℕ, E a a ((⇑(E b a))^[k] v) = -(k : K) • (⇑(E b a))^[k] v := by
    intro k
    induction k with
    | zero => simp [hva]
    | succ k ih =>
      rw [← hstep k, rAA, ih, map_smul]
      push_cast
      module
  have hB : ∀ k : ℕ, E b b ((⇑(E b a))^[k] v) = (k : K) • (⇑(E b a))^[k] v := by
    intro k
    induction k with
    | zero => simp [hvb]
    | succ k ih =>
      rw [← hstep k, rBB, ih, map_smul]
      push_cast
      module
  have hC : ∀ k : ℕ, E a b ((⇑(E b a))^[k+1] v) = -((k : K) * ((k : K) + 1)) • (⇑(E b a))^[k] v := by
    intro k
    induction k with
    | zero =>
      rw [← hstep 0, rEF]
      simp [he, hva, hvb]
    | succ k ih =>
      rw [← hstep (k+1), rEF, ih, map_smul, hstep k, hA (k+1), hB (k+1)]
      push_cast
      module
  have hex : ∃ k : ℕ, (⇑(E b a))^[k+1] v = 0 := by
    by_contra hne
    push_neg at hne
    have hli : LinearIndependent K (fun k : ℕ => (⇑(E b a))^[k+1] v) := by
      refine Module.End.eigenvectors_linearIndependent' (E a a)
        (fun k : ℕ => -(((k+1 : ℕ) : K))) ?_ _ ?_
      · intro i j hij
        simpa using hij
      · intro k
        rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
        exact ⟨hA (k+1), hne k⟩
    haveI := hli.finite
    exact not_finite ℕ
  have hdown : ∀ j : ℕ, (⇑(E b a))^[j+1] v = 0 → E b a v = 0 := by
    intro j
    induction j with
    | zero => intro h; simpa using h
    | succ j ih =>
      intro h
      apply ih
      have h2 := hC (j+1)
      rw [h, map_zero] at h2
      have hc : -(((j+1 : ℕ) : K) * (((j+1 : ℕ) : K) + 1)) ≠ 0 := by
        rw [neg_ne_zero]
        refine mul_ne_zero ?_ ?_
        · exact_mod_cast Nat.succ_ne_zero j
        · exact_mod_cast Nat.succ_ne_zero (j+1)
      exact (smul_eq_zero.mp h2.symm).resolve_left hc
  obtain ⟨k, hk⟩ := hex
  exact hdown k hk

def commonKernelOperators (E : GLOps n K V) : Submodule K V := ⨅ a, ⨅ b, LinearMap.ker (E a b)

theorem mem_common_kernel_iff {E : GLOps n K V} {x : V} : x ∈ commonKernelOperators E ↔ ∀ a b, E a b x = 0 := by
  simp only [commonKernelOperators, Submodule.mem_iInf, LinearMap.mem_ker]

theorem enveloping_preserves_common_kernel {E : GLOps n K V} {u : Module.End K V} (hu : u ∈ Umon E) :
    ∀ y ∈ commonKernelOperators E, u y ∈ commonKernelOperators E := by
  have hu' : u ∈ Submonoid.closure (Set.range fun ab : Fin n × Fin n => E ab.1 ab.2) := hu
  clear hu
  induction hu' using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    intro y hy
    show E a b y ∈ commonKernelOperators E
    rw [mem_common_kernel_iff.mp hy a b]
    exact zero_mem _
  | one => intro y hy; exact hy
  | mul x z _ _ ihx ihz => intro y hy; exact ihx _ (ihz y hy)

theorem trivial_isotypic_invariant_holds [CharZero K] [FiniteDimensional K V] {E : GLOps n K V} (hE : IsGLRep E) : TrivialIsotypicIsInvariant E := by
  have hle : isoSub E 0 ≤ commonKernelOperators E := by
    unfold isoSub
    rw [Submodule.span_le]
    rintro x ⟨u, hu, v, hv, rfl⟩
    refine enveloping_preserves_common_kernel hu v ?_
    rw [mem_common_kernel_iff]
    intro a b
    rcases lt_trichotomy a b with h | rfl | h
    · exact hv.2.2 a b h
    · simpa using (mem_weightSpace_iff_diag_eigen.mp hv.2.1) a
    · exact weight_zero_lowering_kills_raising hE hv.2.1 b a (ne_of_lt h) (hv.2.2 b a h)
  intro x hx
  have hx0 := mem_common_kernel_iff.mp (hle hx)
  refine ⟨mem_weightSpace_iff_diag_eigen.mpr fun a => ?_, fun a b _ => hx0 a b⟩
  simp [hx0 a a]

def loweringWordMonoid (E : GLOps n K V) : Submonoid (Module.End K V) :=
  Submonoid.closure {F | ∃ a b : Fin n, b < a ∧ F = E a b}

def loweringWordSpan (E : GLOps n K V) (v : V) : Submodule K V :=
  Submodule.span K {x | ∃ u ∈ loweringWordMonoid E, x = u v}

theorem lowering_word_span_lowering_stable {E : GLOps n K V} {v : V} {a b : Fin n} (hab : b < a) :
    ∀ y ∈ loweringWordSpan E v, E a b y ∈ loweringWordSpan E v := by
  intro y hy
  have key : loweringWordSpan E v ≤ (loweringWordSpan E v).comap (E a b) := by
    unfold loweringWordSpan
    rw [Submodule.span_le]
    rintro x ⟨u, hu, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    exact Submodule.subset_span ⟨E a b * u, mul_mem (Submonoid.subset_closure ⟨a, b, hab, rfl⟩) hu, rfl⟩
  exact key hy

theorem lowering_word_span_operator_mem {E : GLOps n K V} (hE : IsGLRep E) {mu : Fin n → ℤ} {v : V} (hv : IsHWV E mu v)
    {u : Module.End K V} (hu : u ∈ loweringWordMonoid E) : ∀ c d, E c d (u v) ∈ loweringWordSpan E v := by
  have hmem : ∀ w ∈ loweringWordMonoid E, w v ∈ loweringWordSpan E v := fun w hw => Submodule.subset_span ⟨w, hw, rfl⟩
  have main : ∀ w ∈ loweringWordMonoid E, (∀ c d, E c d (w v) ∈ loweringWordSpan E v) →
      ∀ c d, E c d (u (w v)) ∈ loweringWordSpan E v := by
    have hu' : u ∈ Submonoid.closure {F | ∃ a b : Fin n, b < a ∧ F = E a b} := hu
    clear hu
    induction hu' using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨a, b, hab, rfl⟩ := hx
      intro w hw hwY c d
      have h := LinearMap.congr_fun (hE.1 c d a b) (w v)
      rw [LinearMap.sub_apply, LinearMap.sub_apply] at h
      have h2 := sub_eq_iff_eq_add.mp h
      rw [show E c d (E a b (w v)) = (E c d * E a b) (w v) from rfl, h2]
      refine add_mem (sub_mem ?_ ?_) (lowering_word_span_lowering_stable hab _ (hwY c d))
      · split_ifs
        · exact hwY c b
        · rw [LinearMap.zero_apply]; exact zero_mem _
      · split_ifs
        · exact hwY a d
        · rw [LinearMap.zero_apply]; exact zero_mem _
    | one => intro w hw hwY c d; exact hwY c d
    | mul x z _ hz ihx ihz =>
      intro w hw hwY c d
      exact ihx (z * w) (mul_mem hz hw) (ihz w hw hwY) c d
  have base : ∀ c d, E c d ((1 : Module.End K V) v) ∈ loweringWordSpan E v := by
    intro c d
    show E c d v ∈ _
    rcases lt_trichotomy c d with h | rfl | h
    · rw [hv.2.2 c d h]; exact zero_mem _
    · rw [(mem_weightSpace_iff_diag_eigen.mp hv.2.1) c]
      exact Submodule.smul_mem _ _ (hmem 1 (one_mem _))
    · exact hmem (E c d) (Submonoid.subset_closure ⟨c, d, h, rfl⟩)
  intro c d
  exact main 1 (one_mem _) base c d

theorem lowering_word_span_gl_stable {E : GLOps n K V} (hE : IsGLRep E) {mu : Fin n → ℤ} {v : V} (hv : IsHWV E mu v)
    (c d : Fin n) : ∀ y ∈ loweringWordSpan E v, E c d y ∈ loweringWordSpan E v := by
  intro y hy
  have key : loweringWordSpan E v ≤ (loweringWordSpan E v).comap (E c d) := by
    unfold loweringWordSpan
    rw [Submodule.span_le]
    rintro x ⟨u, hu, rfl⟩
    exact lowering_word_span_operator_mem hE hv hu c d
  exact key hy

theorem lowering_word_span_enveloping_stable {E : GLOps n K V} (hE : IsGLRep E) {mu : Fin n → ℤ} {v : V} (hv : IsHWV E mu v)
    {u : Module.End K V} (hu : u ∈ Umon E) : ∀ y ∈ loweringWordSpan E v, u y ∈ loweringWordSpan E v := by
  have hu' : u ∈ Submonoid.closure (Set.range fun ab : Fin n × Fin n => E ab.1 ab.2) := hu
  clear hu
  induction hu' using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    intro y hy
    exact lowering_word_span_gl_stable hE hv a b y hy
  | one => intro y hy; exact hy
  | mul x z _ _ ihx ihz => intro y hy; exact ihx _ (ihz y hy)

theorem lowering_word_weight_or_nMinus {E : GLOps n K V} (hs : OperatorsShiftWeightsByRoots E) {mu : Fin n → ℤ} {v : V}
    (hv : v ∈ weightSp E mu) {u : Module.End K V} (hu : u ∈ loweringWordMonoid E) :
    (∃ ν, u v ∈ weightSp E ν) ∧ (u v = v ∨ u v ∈ nMinus E) := by
  have hu' : u ∈ Submonoid.closure {F | ∃ a b : Fin n, b < a ∧ F = E a b} := hu
  clear hu
  induction hu' using Submonoid.closure_induction generalizing mu v with
  | mem x hx =>
    obtain ⟨a, b, hab, rfl⟩ := hx
    refine ⟨⟨mu + rootW a b, hs a b mu v hv⟩, Or.inr ?_⟩
    have hle : LinearMap.range (E a b) ≤ nMinus E := by
      unfold nMinus
      exact le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le hab le_rfl))
    exact hle (LinearMap.mem_range_self _ v)
  | one => exact ⟨⟨mu, hv⟩, Or.inl rfl⟩
  | mul x z _ _ ihx ihz =>
    obtain ⟨⟨ν, hν⟩, h1⟩ := ihz (mu := mu) (v := v) hv
    obtain ⟨⟨ν', hν'⟩, h2⟩ := ihx (mu := ν) (v := z v) hν
    refine ⟨⟨ν', hν'⟩, ?_⟩
    rcases h2 with h2 | h2
    · rcases h1 with h1 | h1
      · left; exact h2.trans h1
      · right
        rw [show (x * z) v = x (z v) from rfl, h2]
        exact h1
    · right; exact h2

theorem nontrivial_isotypic_weight_zero_killed {E : GLOps n K V} (hE : IsGLRep E) (hs : OperatorsShiftWeightsByRoots E) : NontrivialIsotypicWeightZeroKilled E := by
  intro P π hπ hP mu hmu x hx
  have hY : ∀ v, IsHWV E mu v → ∀ y ∈ loweringWordSpan E v, P (π y) = 0 := by
    intro v hv
    have key : loweringWordSpan E v ≤ LinearMap.ker (P * π) := by
      unfold loweringWordSpan
      rw [Submodule.span_le]
      rintro y ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      show P (π (w v)) = 0
      obtain ⟨⟨ν, hν⟩, h⟩ := lowering_word_weight_or_nMinus hs hv.2.1 hw
      rcases h with h | h
      · rw [h, hπ.2 mu hmu v hv.2.1, map_zero]
      · by_cases hν0 : ν = 0
        · subst hν0
          rw [hπ.1 _ hν]
          exact hP _ hν h
        · rw [hπ.2 ν hν0 _ hν, map_zero]
    intro y hy
    exact LinearMap.mem_ker.mp (key hy)
  have hiso : isoSub E mu ≤ LinearMap.ker (P * π) := by
    unfold isoSub
    rw [Submodule.span_le]
    rintro y ⟨u, hu, v, hv, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    show P (π (u v)) = 0
    exact hY v hv (u v) (lowering_word_span_enveloping_stable hE hv hu v (Submodule.subset_span ⟨1, one_mem _, rfl⟩))
  exact LinearMap.mem_ker.mp (hiso hx)

end Formalism.MainNotions.G.GLWeightTheory
