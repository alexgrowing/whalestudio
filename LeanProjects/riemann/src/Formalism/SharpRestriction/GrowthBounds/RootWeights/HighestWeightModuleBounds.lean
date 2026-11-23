import Formalism.SharpRestriction.GrowthBounds.RootWeights.StableSubspaceCompleteReducibility

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem v2rep_mem_weightSp (E : GLOps n K V) (mu : Fin n → ℤ) (x : V) :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero]

theorem v2rep_comm (E : GLOps n K V) (hR : SatisfiesGLRelations E) (a b c d : Fin n) (x : V) :
    E a b (E c d x) = E c d (E a b x) + ((if b = c then E a d x else 0) - (if d = a then E c b x else 0)) := by
  have h := congrArg (fun f : Module.End K V => f x) (hR a b c d)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [sub_eq_iff_eq_add'] at h
  rw [h]
  congr 1
  split_ifs <;> simp

theorem v2rep_shift (E : GLOps n K V) (hR : SatisfiesGLRelations E) (a b : Fin n) (ν : Fin n → ℤ) (x : V)
    (hx : x ∈ weightSp E ν) : E a b x ∈ weightSp E (ν + rootW a b) := by
  rw [v2rep_mem_weightSp] at hx ⊢
  intro c
  rw [v2rep_comm E hR c c a b x, hx c, map_smul]
  by_cases hca : c = a <;> by_cases hcb : c = b
  · subst hca; subst hcb
    simp [rootW]
  · subst hca
    simp [rootW, hcb, Ne.symm hcb]
    module
  · subst hcb
    simp [rootW, hca]
    module
  · simp [rootW, hca, hcb, Ne.symm hcb]

def cyclicLevelSubmodule (E : GLOps n K V) (v : V) : ℕ → Submodule K V
  | 0 => Submodule.span K {v}
  | k + 1 => cyclicLevelSubmodule E v k ⊔ ⨆ ab : Fin n × Fin n, ⨆ (_ : ab.2 < ab.1), (cyclicLevelSubmodule E v k).map (E ab.1 ab.2)

theorem v2rep_Y_le (E : GLOps n K V) (v : V) (k : ℕ) : cyclicLevelSubmodule E v k ≤ cyclicLevelSubmodule E v (k + 1) := by
  exact le_sup_left

theorem v2rep_Y_low (E : GLOps n K V) (v : V) (k : ℕ) (a b : Fin n) (h : b < a) (x : V) (hx : x ∈ cyclicLevelSubmodule E v k) :
    E a b x ∈ cyclicLevelSubmodule E v (k + 1) := by
  show E a b x ∈ cyclicLevelSubmodule E v k ⊔ _
  refine Submodule.mem_sup_right ?_
  refine Submodule.mem_iSup_of_mem (a, b) ?_
  refine Submodule.mem_iSup_of_mem h ?_
  exact Submodule.mem_map_of_mem hx

theorem v2rep_Y_up (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (v : V) (hv : IsHWV E mu v) (k : ℕ) :
    ∀ c d : Fin n, c ≤ d → ∀ x ∈ cyclicLevelSubmodule E v k, E c d x ∈ cyclicLevelSubmodule E v k := by
  induction k with
  | zero =>
    intro c d hcd x hx
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    rcases hcd.lt_or_eq with hlt | heq
    · rw [hv.2.2 c d hlt]
      exact Submodule.zero_mem _
    · subst heq
      rw [(v2rep_mem_weightSp E mu v).1 hv.2.1 c]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  | succ k ih =>
    have hany : ∀ p q : Fin n, ∀ y ∈ cyclicLevelSubmodule E v k, E p q y ∈ cyclicLevelSubmodule E v (k + 1) := by
      intro p q y hy
      rcases lt_or_ge q p with hqp | hpq
      · exact v2rep_Y_low E v k p q hqp y hy
      · exact v2rep_Y_le E v k (ih p q hpq y hy)
    intro c d hcd
    suffices hs : cyclicLevelSubmodule E v (k + 1) ≤ (cyclicLevelSubmodule E v (k + 1)).comap (E c d) from fun x hx => hs hx
    refine sup_le (fun y hy => v2rep_Y_le E v k (ih c d hcd y hy)) ?_
    refine iSup_le fun ab => iSup_le fun hab => ?_
    rw [Submodule.map_le_iff_le_comap]
    intro y hy
    rw [Submodule.mem_comap, Submodule.mem_comap, v2rep_comm E hR c d ab.1 ab.2 y]
    refine Submodule.add_mem _ (v2rep_Y_low E v k ab.1 ab.2 hab _ (ih c d hcd y hy)) ?_
    refine Submodule.sub_mem _ ?_ ?_
    · split_ifs
      · exact hany c ab.2 y hy
      · exact Submodule.zero_mem _
    · split_ifs
      · exact hany ab.1 d y hy
      · exact Submodule.zero_mem _

theorem v2rep_Y_all (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (v : V) (hv : IsHWV E mu v) (k : ℕ)
    (a b : Fin n) (y : V) (hy : y ∈ cyclicLevelSubmodule E v k) : E a b y ∈ cyclicLevelSubmodule E v (k + 1) := by
  rcases lt_or_ge b a with hba | hab
  · exact v2rep_Y_low E v k a b hba y hy
  · exact v2rep_Y_le E v k (v2rep_Y_up E hR mu v hv k a b hab y hy)

theorem v2rep_Umon_Y (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (v : V) (hv : IsHWV E mu v)
    (u : Module.End K V) (hu : u ∈ Umon E) : ∀ k, ∀ x ∈ cyclicLevelSubmodule E v k, ∃ k', u x ∈ cyclicLevelSubmodule E v k' := by
  induction hu using Submonoid.closure_induction with
  | mem u hu =>
    obtain ⟨ab, rfl⟩ := hu
    intro k x hx
    exact ⟨k + 1, v2rep_Y_all E hR mu v hv k ab.1 ab.2 x hx⟩
  | one =>
    intro k x hx
    exact ⟨k, hx⟩
  | mul u₁ u₂ _ _ h₁ h₂ =>
    intro k x hx
    obtain ⟨k₂, hk₂⟩ := h₂ k x hx
    obtain ⟨k₁, hk₁⟩ := h₁ k₂ _ hk₂
    exact ⟨k₁, hk₁⟩

def dominantWeightSubmodule [NeZero n] (E : GLOps n K V) (mu : Fin n → ℤ) : Submodule K V :=
  ⨆ ν ∈ {ν : Fin n → ℤ | mu (lastIdx n) ≤ ν (lastIdx n) ∧ ν 0 ≤ mu 0}, weightSp E ν

theorem v2rep_Good_low [NeZero n] (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (a b : Fin n) (h : b < a) :
    dominantWeightSubmodule E mu ≤ (dominantWeightSubmodule E mu).comap (E a b) := by
  refine iSup₂_le fun ν hν => ?_
  intro x hx
  rw [Submodule.mem_comap]
  have hs := v2rep_shift E hR a b ν x hx
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0] at h
    exact absurd h (Fin.not_lt_zero b)
  have hbl : b ≠ lastIdx n := by
    intro hb
    have : (a : ℕ) ≤ n - 1 := Nat.le_sub_one_of_lt a.2
    have h2 : (b : ℕ) < a := h
    rw [hb] at h2
    simp [lastIdx] at h2
    omega
  refine (le_iSup₂ (f := fun ν (_ : ν ∈ {ν : Fin n → ℤ | mu (lastIdx n) ≤ ν (lastIdx n) ∧ ν 0 ≤ mu 0}) =>
    weightSp E ν) (ν + rootW a b) ?_) hs
  obtain ⟨h1, h2⟩ := hν
  refine ⟨?_, ?_⟩
  · simp only [Pi.add_apply, rootW, Pi.sub_apply, Pi.single_apply, Ne.symm hbl, if_false, sub_zero]
    split_ifs <;> omega
  · simp only [Pi.add_apply, rootW, Pi.sub_apply, Pi.single_apply, Ne.symm ha0, if_false, zero_sub]
    split_ifs <;> omega

theorem v2rep_Y_Good [NeZero n] (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (v : V) (hv : IsHWV E mu v)
    (k : ℕ) : cyclicLevelSubmodule E v k ≤ dominantWeightSubmodule E mu := by
  induction k with
  | zero =>
    refine (Submodule.span_singleton_le_iff_mem _ _).2 ?_
    exact (le_iSup₂ (f := fun ν (_ : ν ∈ {ν : Fin n → ℤ | mu (lastIdx n) ≤ ν (lastIdx n) ∧ ν 0 ≤ mu 0}) =>
      weightSp E ν) mu ⟨le_rfl, le_rfl⟩) hv.2.1
  | succ k ih =>
    refine sup_le ih (iSup_le fun ab => iSup_le fun hab => ?_)
    rw [Submodule.map_le_iff_le_comap]
    exact ih.trans (v2rep_Good_low E hR mu ab.1 ab.2 hab)

theorem highest_weight_module_bounds : HighestWeightModuleWeightBounds := by
  intro K V _ _ _ _ n _ E hR mu v hv u hu
  obtain ⟨k, hk⟩ := v2rep_Umon_Y E hR mu v hv u hu 0 v (Submodule.mem_span_singleton_self v)
  exact v2rep_Y_Good E hR mu v hv k hk

end Formalism.MainNotions.G.GLWeightTheory
