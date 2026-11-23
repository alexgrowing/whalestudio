import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.GeneratedSubmoduleStableUnderAction
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.ExistsIrreducibleHighestWeightSubmodule
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem pi_submodule_finiteDimensional {M : Type*} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) [FiniteDimensional ℂ S] :
    FiniteDimensional ℂ (Submodule.pi Set.univ fun _ : Fin n => S) := by
  let g : (Fin n → S) →ₗ[ℂ] (Fin n → M) := LinearMap.pi fun c => S.subtype ∘ₗ LinearMap.proj c
  have : Submodule.pi Set.univ (fun _ : Fin n => S) = LinearMap.range g := by
    ext f
    constructor
    · intro hf
      exact ⟨fun c => ⟨f c, mem_pi_submodule_iff.1 hf c⟩, rfl⟩
    · rintro ⟨w, rfl⟩
      exact mem_pi_submodule_iff.2 fun c => by simp [g]
  rw [this]
  infer_instance

section HidaSetting

variable {ε : Fin n → Bool} {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
  {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℂ N] {EN : Fin n → Fin n → Module.End ℂ N}
  {φ : (Fin n → M) →ₗ[ℂ] N} {θ : ℝ}

theorem eigenspace_K_finite (hE : IsGlRep E) (hVfd : FiniteDimensional ℂ V) (hVk : IsKStableSub ε E V)
    {x : Fin n → M} (hx : x ∈ Xs (eeVd E) (genSub E V) θ) :
    ∃ S : Submodule ℂ (Fin n → M), S ≤ Xs (eeVd E) (genSub E V) θ ∧ FiniteDimensional ℂ S ∧
      IsKStableSub ε (tensVd E) S ∧ x ∈ S := by
  classical
  have hxg := (mem_euler_eigenspace_iff.1 hx).1
  have hGs : ∀ a b, ∀ v ∈ genSub E V, E a b v ∈ genSub E V := fun a b v hv => generated_submodule_stable_under_action V a b hv
  choose m hm using fun c => exists_layer_of_mem_genSub hE hVk (hxg c)
  set K := Finset.univ.sup m
  have hxK : ∀ c, x c ∈ layer ε E V K := fun c => layer_mono (Finset.le_sup (mem_univ c)) (hm c)
  have hfdL : FiniteDimensional ℂ (layer ε E V K) := finiteDimensional_layer hVfd K
  have hLk := layer_kStable hE hVk K
  have := pi_submodule_finiteDimensional (n := n) (layer ε E V K)
  refine ⟨Submodule.pi Set.univ (fun _ => layer ε E V K) ⊓ Xs (eeVd E) (genSub E V) θ, inf_le_right,
    Submodule.finiteDimensional_of_le inf_le_left, ?_, ⟨mem_pi_submodule_iff.2 hxK, hx⟩⟩
  intro a b hab f hf
  refine ⟨mem_pi_submodule_iff.2 fun c => ?_, euler_eigenspace_stable_under_action hE hGs a b hf.2⟩
  rw [tensor_dual_action_apply_component]
  refine sub_mem (hLk a b hab _ (mem_pi_submodule_iff.1 hf.1 c)) ?_
  split_ifs
  · exact mem_pi_submodule_iff.1 hf.1 a
  · exact zero_mem _

theorem image_eigenspace_K_finite (hE : IsGlRep E) (hVfd : FiniteDimensional ℂ V) (hVk : IsKStableSub ε E V)
    (hφ : ∀ (a b : Fin n) (f : Fin n → M), (∀ c, f c ∈ genSub E V) → φ (tensVd E a b f) = EN a b (φ f))
    {y : N} (hy : y ∈ (Xs (eeVd E) (genSub E V) θ).map φ) :
    ∃ T : Submodule ℂ N, T ≤ (Xs (eeVd E) (genSub E V) θ).map φ ∧ FiniteDimensional ℂ T ∧
      IsKStableSub ε EN T ∧ y ∈ T := by
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
  obtain ⟨S, hSX, hfd, hSk, hxS⟩ := eigenspace_K_finite hE hVfd hVk hx
  refine ⟨S.map φ, Submodule.map_mono hSX, inferInstance, ?_, Submodule.mem_map_of_mem hxS⟩
  intro a b hab v hv
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hv
  rw [← hφ a b f (mem_euler_eigenspace_iff.1 (hSX hf)).1]
  exact Submodule.mem_map_of_mem (hSk a b hab f hf)

theorem image_weights_in_root_cone (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hVfd : FiniteDimensional ℂ V)
    (hVk : IsKStableSub ε E V)
    (hφ : ∀ (a b : Fin n) (f : Fin n → M), (∀ c, f c ∈ genSub E V) → φ (tensVd E a b f) = EN a b (φ f))
    {Λ : Fin n → ℝ}
    (hK2 : ∀ (μ : Fin n → ℝ) (f : Fin n → M), f ∈ Xs (eeVd E) (genSub E V) θ → f ≠ 0 →
      IsKHWVec ε (tensVd E) μ f → InRootCone (μ - Λ))
    {μ : Fin n → ℝ} {y : N} (hy : y ∈ (Xs (eeVd E) (genSub E V) θ).map φ) (hy0 : y ≠ 0)
    (hμ : IsKHWVec ε EN μ y) : InRootCone (μ - Λ) := by
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
  obtain ⟨S, hSX, hfd, hSk, hxS⟩ := eigenspace_K_finite hE hVfd hVk hx
  obtain ⟨x1, hx1S, hkhw, hfx⟩ := exists_highest_weight_lift_pi (isKUnitary_of_isInfUnitary hU) φ hfd hSk
    (fun a b _ z hz => hφ a b z (mem_euler_eigenspace_iff.1 (hSX hz)).1) hxS hμ
  have hx10 : x1 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hfx
    exact hy0 hfx.symm
  exact hK2 μ x1 (hSX hx1S) hx10 hkhw

end HidaSetting

section Gen

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
  {N : Type*} [AddCommGroup N] [Module ℂ N] {EN : Fin n → Fin n → Module.End ℂ N}

theorem exists_commuting_projection_image (V : Submodule ℂ M)
    (hGen : ∀ f : Fin n → M, (∀ c, f c ∈ genSub E V) →
      f ∈ genSub (tensVd E) (Submodule.pi Set.univ fun _ => V))
    (P : Module.End ℂ (Fin n → M)) (hPg : ∀ f : Fin n → M, (∀ c, f c ∈ genSub E V) → ∀ c, P f c ∈ genSub E V)
    (hPc : ∀ a b, Commute P (tensVd E a b)) (φ : (Fin n → M) →ₗ[ℂ] N)
    (hφ : ∀ (a b : Fin n) (f : Fin n → M), (∀ c, f c ∈ genSub E V) → φ (tensVd E a b f) = EN a b (φ f))
    {x : Fin n → M} (hx : ∀ c, x c ∈ genSub E V) (hPx : φ (P x) ≠ 0) :
    ∃ u : Fin n → M, (∀ c, u c ∈ V) ∧ φ (P u) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hGs : ∀ a b, ∀ v ∈ genSub E V, E a b v ∈ genSub E V := fun a b v hv => generated_submodule_stable_under_action V a b hv
  set T : Submodule ℂ (Fin n → M) :=
    Submodule.pi Set.univ (fun _ => genSub E V) ⊓ LinearMap.ker (φ ∘ₗ P) with hT
  have hle : genSub (tensVd E) (Submodule.pi Set.univ fun _ => V) ≤ T := by
    unfold genSub
    refine sInf_le ⟨fun u hu => ⟨mem_pi_submodule_iff.2 fun c => le_generatedSubmodule_dual V (mem_pi_submodule_iff.1 hu c), ?_⟩,
      fun a b v hv => ⟨mem_pi_submodule_iff.2 (dualTensorAction_mem hGs a b (mem_pi_submodule_iff.1 hv.1)), ?_⟩⟩
    · exact LinearMap.mem_ker.2 (hcon u (mem_pi_submodule_iff.1 hu))
    · have hv2 : φ (P v) = 0 := LinearMap.mem_ker.1 hv.2
      refine LinearMap.mem_ker.2 ?_
      rw [LinearMap.comp_apply]
      have hc := (hPc a b).eq
      have : P (tensVd E a b v) = tensVd E a b (P v) := by
        rw [← Module.End.mul_apply, hc, Module.End.mul_apply]
      rw [this, hφ a b _ (hPg v (mem_pi_submodule_iff.1 hv.1)), hv2, map_zero]
  have hxT := hle (hGen x hx)
  exact hPx (LinearMap.mem_ker.1 hxT.2)

end Gen

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
