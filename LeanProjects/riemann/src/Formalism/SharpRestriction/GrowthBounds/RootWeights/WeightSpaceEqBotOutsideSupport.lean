import Formalism.SharpRestriction.GrowthBounds.RootWeights.CyclicSubmoduleIsSubrepresentation

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section wt
variable {n : ℕ} {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem mem_weightSp_iff_diagonal_apply (E : GLOps n K V) (mu : Fin n → ℤ) (x : V) :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  simp [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem linearMap_ext_on_weightSpaces {V' : Type} [AddCommGroup V'] [Module K V'] (E : GLOps n K V) (hE : IsGLRep E)
    (f g : V →ₗ[K] V') (h : ∀ mu, ∀ x ∈ weightSp E mu, f x = g x) : f = g := by
  have hle : (⨆ mu, weightSp E mu) ≤ LinearMap.eqLocus f g := iSup_le fun mu x hx => h mu x hx
  ext x
  have : x ∈ (⨆ mu, weightSp E mu) := by rw [hE.2.2]; trivial
  exact hle this

open Classical in

def lagrangeWeightFactor (E : GLOps n K V) (mu nu : Fin n → ℤ) : Module.End K V :=
  if h : ∃ a, nu a ≠ mu a then
    (((mu h.choose : K) - (nu h.choose : K))⁻¹) • (E h.choose h.choose - (nu h.choose : K) • (1 : Module.End K V))
  else 1

def lagrangeOperator (E : GLOps n K V) (mu : Fin n → ℤ) : List (Fin n → ℤ) → Module.End K V
  | [] => 1
  | nu :: l => lagrangeWeightFactor E mu nu * lagrangeOperator E mu l

theorem lagrangeFactor_acts_by_scalar (E : GLOps n K V) (mu nu ka : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E ka) :
    ∃ c : K, lagrangeWeightFactor E mu nu x = c • x := by
  unfold lagrangeWeightFactor
  split_ifs with h
  · refine ⟨((mu h.choose : K) - (nu h.choose : K))⁻¹ * ((ka h.choose : K) - (nu h.choose : K)), ?_⟩
    simp [(mem_weightSp_iff_diagonal_apply E ka x).1 hx, sub_smul, mul_smul, smul_sub]
  · exact ⟨1, by simp⟩

theorem lagrangeFactor_fixes_own_weight [CharZero K] (E : GLOps n K V) (mu nu : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E mu) :
    lagrangeWeightFactor E mu nu x = x := by
  unfold lagrangeWeightFactor
  split_ifs with h
  · have hne : ((mu h.choose : K) - (nu h.choose : K)) ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast (h.choose_spec).symm
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, (mem_weightSp_iff_diagonal_apply E mu x).1 hx, Module.End.one_apply]
    rw [← sub_smul, smul_smul, inv_mul_cancel₀ hne, one_smul]
  · simp

theorem lagrangeFactor_kills_other_weight (E : GLOps n K V) (mu nu : Fin n → ℤ) (hne : nu ≠ mu) (x : V) (hx : x ∈ weightSp E nu) :
    lagrangeWeightFactor E mu nu x = 0 := by
  have h : ∃ a, nu a ≠ mu a := by
    by_contra hc; exact hne (funext fun a => by_contra fun h => hc ⟨a, h⟩)
  unfold lagrangeWeightFactor
  rw [dif_pos h]
  simp [(mem_weightSp_iff_diagonal_apply E nu x).1 hx]

theorem lagrangeFactor_preserves_stable (E : GLOps n K V) (mu nu : Fin n → ℤ) (W : Submodule K V)
    (hW : ∀ a, ∀ x ∈ W, E a a x ∈ W) (x : V) (hx : x ∈ W) : lagrangeWeightFactor E mu nu x ∈ W := by
  unfold lagrangeWeightFactor
  split_ifs with h
  · simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply]
    exact W.smul_mem _ (W.sub_mem (hW _ x hx) (W.smul_mem _ hx))
  · simpa using hx

theorem lagrangeOperator_acts_by_scalar (E : GLOps n K V) (mu ka : Fin n → ℤ) (l : List (Fin n → ℤ)) (x : V)
    (hx : x ∈ weightSp E ka) : ∃ c : K, lagrangeOperator E mu l x = c • x := by
  induction l with
  | nil => exact ⟨1, by simp [lagrangeOperator]⟩
  | cons nu l ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨c', hc'⟩ := lagrangeFactor_acts_by_scalar E mu nu ka x hx
    exact ⟨c * c', by simp [lagrangeOperator, hc, hc', smul_smul]⟩

theorem lagrangeOperator_fixes_own_weight [CharZero K] (E : GLOps n K V) (mu : Fin n → ℤ) (l : List (Fin n → ℤ)) (x : V)
    (hx : x ∈ weightSp E mu) : lagrangeOperator E mu l x = x := by
  induction l with
  | nil => simp [lagrangeOperator]
  | cons nu l ih => simp [lagrangeOperator, ih, lagrangeFactor_fixes_own_weight E mu nu x hx]

theorem lagrangeOperator_kills_listed (E : GLOps n K V) (mu ka : Fin n → ℤ) (hne : ka ≠ mu) (l : List (Fin n → ℤ))
    (hl : ka ∈ l) (x : V) (hx : x ∈ weightSp E ka) : lagrangeOperator E mu l x = 0 := by
  induction l with
  | nil => simp at hl
  | cons nu l ih =>
    obtain ⟨c, hc⟩ := lagrangeOperator_acts_by_scalar E mu ka l x hx
    rcases List.mem_cons.1 hl with h | h
    · subst h
      simp [lagrangeOperator, hc, lagrangeFactor_kills_other_weight E mu ka hne x hx]
    · simp [lagrangeOperator, ih h]

theorem lagrangeOperator_preserves_stable (E : GLOps n K V) (mu : Fin n → ℤ) (l : List (Fin n → ℤ)) (W : Submodule K V)
    (hW : ∀ a, ∀ x ∈ W, E a a x ∈ W) (x : V) (hx : x ∈ W) : lagrangeOperator E mu l x ∈ W := by
  induction l with
  | nil => simpa [lagrangeOperator] using hx
  | cons nu l ih => simpa [lagrangeOperator] using lagrangeFactor_preserves_stable E mu nu W hW _ ih

theorem finitely_many_weights_span [FiniteDimensional K V] (E : GLOps n K V) (hE : IsGLRep E) :
    ∃ s : Finset (Fin n → ℤ), (⨆ mu ∈ s, weightSp E mu) = ⊤ := by
  have hc : IsCompactElement (⊤ : Submodule K V) :=
    (Submodule.fg_iff_compact _).1 (Module.finite_def.1 inferInstance)
  obtain ⟨s, hs⟩ := CompleteLattice.IsCompactElement.exists_finset_of_le_iSup _ hc (weightSp E) (by rw [hE.2.2])
  exact ⟨s, top_le_iff.1 hs⟩

theorem weightSpace_eq_bot_outside_support [CharZero K] (E : GLOps n K V) (s : Finset (Fin n → ℤ))
    (hs : (⨆ mu ∈ s, weightSp E mu) = ⊤) (ka : Fin n → ℤ) (hk : ka ∉ s) : weightSp E ka = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 : lagrangeOperator E ka s.toList x = x := lagrangeOperator_fixes_own_weight E ka _ x hx
  have hle : (⨆ mu ∈ s, weightSp E mu) ≤ LinearMap.ker (lagrangeOperator E ka s.toList) := by
    refine iSup₂_le fun mu hmu y hy => ?_
    exact lagrangeOperator_kills_listed E ka mu (fun h => hk (h ▸ hmu)) _ (Finset.mem_toList.2 hmu) y hy
  have h2 : x ∈ (⨆ mu ∈ s, weightSp E mu) := by rw [hs]; trivial
  have h3 := hle h2
  rw [LinearMap.mem_ker, h1] at h3
  simpa using h3

theorem weight_projections_exist [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (hE : IsGLRep E) :
    ∃ (s : Finset (Fin n → ℤ)) (π : (Fin n → ℤ) → Module.End K V),
      (∀ mu, IsWtProj E mu (π mu)) ∧
      (∀ mu, ∀ W : Submodule K V, (∀ a, ∀ x ∈ W, E a a x ∈ W) → ∀ x ∈ W, π mu x ∈ W) ∧
      (∀ mu, mu ∉ s → weightSp E mu = ⊥) ∧
      (∀ mu x, π mu x ∈ weightSp E mu) ∧
      (∀ x, ∑ mu ∈ s, π mu x = x) := by
  classical
  obtain ⟨s, hs⟩ := finitely_many_weights_span E hE
  have hbot := weightSpace_eq_bot_outside_support E s hs
  have hπ : ∀ mu, IsWtProj E mu (lagrangeOperator E mu s.toList) := by
    intro mu
    refine ⟨fun x hx => lagrangeOperator_fixes_own_weight E mu _ x hx, fun nu hnu x hx => ?_⟩
    by_cases hm : nu ∈ s
    · exact lagrangeOperator_kills_listed E mu nu hnu _ (Finset.mem_toList.2 hm) x hx
    · rw [hbot nu hm] at hx
      rw [(Submodule.mem_bot K).1 hx, map_zero]
  refine ⟨s, fun mu => lagrangeOperator E mu s.toList, hπ, fun mu W hW x hx => lagrangeOperator_preserves_stable E mu _ W hW x hx, hbot, ?_, ?_⟩
  · intro mu x
    have : LinearMap.range (lagrangeOperator E mu s.toList) ≤ weightSp E mu := by
      rw [LinearMap.range_eq_map, ← hE.2.2, Submodule.map_iSup]
      refine iSup_le fun nu => ?_
      rintro _ ⟨y, hy, rfl⟩
      by_cases h : nu = mu
      · subst h; rw [(hπ nu).1 y hy]; exact hy
      · rw [(hπ mu).2 nu h y hy]; exact Submodule.zero_mem _
    exact this ⟨x, rfl⟩
  · intro x
    have : (∑ mu ∈ s, lagrangeOperator E mu s.toList) = (1 : Module.End K V) := by
      refine linearMap_ext_on_weightSpaces E hE _ _ fun nu y hy => ?_
      rw [LinearMap.sum_apply, Module.End.one_apply]
      by_cases hm : nu ∈ s
      · rw [Finset.sum_eq_single nu (fun mu _ hmu => (hπ mu).2 nu (Ne.symm hmu) y hy) (fun h => absurd hm h)]
        exact (hπ nu).1 y hy
      · rw [hbot nu hm] at hy
        rw [(Submodule.mem_bot K).1 hy]; simp
    have h2 := congrArg (fun f : Module.End K V => f x) this
    simpa [LinearMap.sum_apply] using h2

end wt

end Formalism.MainNotions.G.GLWeightTheory
