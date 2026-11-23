import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeKerOfLocalFiniteLengthToSimpleStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqTopOfPureTensorsOfFactorGenerators

open scoped TensorProduct

namespace GlobalTheory.TensHead

section Quot
variable {V : Type} [AddCommGroup V] [Module ℂ V]

noncomputable def quotOp (N : Submodule ℂ V) (f : Module.End ℂ V) : Module.End ℂ (V ⧸ N) := by
  classical
  exact if h : N ≤ N.comap f then N.mapQ N f h else 0

theorem quotOp_mk (N : Submodule ℂ V) (f : Module.End ℂ V) (h : ∀ x ∈ N, f x ∈ N) (x : V) :
    quotOp N f (N.mkQ x) = N.mkQ (f x) := by
  have h' : N ≤ N.comap f := fun x hx => h x hx
  unfold quotOp
  rw [dif_pos h']
  simp

theorem quotOp_mul (N : Submodule ℂ V) (f₁ f₂ : Module.End ℂ V) (h₁ : ∀ x ∈ N, f₁ x ∈ N)
    (h₂ : ∀ x ∈ N, f₂ x ∈ N) : quotOp N f₁ * quotOp N f₂ = quotOp N (f₁ * f₂) := by
  have h₁₂ : ∀ x ∈ N, (f₁ * f₂) x ∈ N := fun x hx => h₁ _ (h₂ x hx)
  apply Submodule.linearMap_qext
  ext x
  simp only [LinearMap.comp_apply, Module.End.mul_apply]
  rw [quotOp_mk N f₂ h₂, quotOp_mk N f₁ h₁, quotOp_mk N _ h₁₂, Module.End.mul_apply]

end Quot

section Slot
variable {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]

theorem piOp_comm (i j : ι) (hij : j ≠ i) (g : Module.End ℂ (M i)) (h : Module.End ℂ (M j)) :
    piOp i g * piOp j h = piOp j h * piOp i g := by
  unfold piOp
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← PiTensorProduct.map_comp,
    ← PiTensorProduct.map_comp]
  congr 1
  funext k
  by_cases hki : k = i
  · subst hki
    simp [Function.update_of_ne hij.symm]
  · by_cases hkj : k = j
    · subst hkj
      simp [Function.update_of_ne hij]
    · simp [Function.update_of_ne hki, Function.update_of_ne hkj]

end Slot

end GlobalTheory.TensHead

namespace GlobalTheory.TensHead

theorem position_mem_of_maximal_stable : ∀ {ι : Type} [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀]
    {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (Op₀ : Set (Module.End ℂ M₀)) (Op : ∀ i, Set (Module.End ℂ (M i))) (i : ι)
    (Rel K : Submodule ℂ (M i)),
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (M i)), StrictMono N →
        (∀ j, Rel ≤ N j ∧ ∀ g ∈ Op i, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    (∀ N : Submodule ℂ (M i), Rel ≤ N → GlobalTheory.TensHead.Stab (Op i) N → N ≠ ⊤ → N ≤ K) →
    K ≠ ⊤ → GlobalTheory.TensHead.Stab (Op i) K →
    ∀ N' : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] j, M j)),
      (∀ x ∈ Rel, ∀ (x₀ : M₀) (y : ∀ j, M j),
        x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N') →
      GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps Op₀ (GlobalTheory.TensHead.piOps Op)) N' →
      (∀ U, GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps Op₀ (GlobalTheory.TensHead.piOps Op)) U → N' ≤ U →
        U = N' ∨ U = ⊤) →
      ∀ x ∈ K, ∀ (x₀ : M₀) (y : ∀ j, M j),
        x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N' := by
  intro ι _ M₀ _ _ M _ _ Op₀ Op i Rel K hlen hmax hK hKst N' hRel hN'st hN'max x hx x₀ y
  let φ : M i →ₗ[ℂ] (M₀ ⊗[ℂ] (⨂[ℂ] j, M j)) ⧸ N' :=
    N'.mkQ ∘ₗ (TensorProduct.mk ℂ M₀ (⨂[ℂ] j, M j) x₀) ∘ₗ
      ((PiTensorProduct.tprod ℂ : MultilinearMap ℂ M (⨂[ℂ] j, M j)).toLinearMap y i)
  have hφ : ∀ z, φ z = N'.mkQ (x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i z)) := by
    intro z
    simp [φ, MultilinearMap.toLinearMap_apply]
  let act : Module.End ℂ (M i) → Module.End ℂ ((M₀ ⊗[ℂ] (⨂[ℂ] j, M j)) ⧸ N') :=
    fun g => quotOp N' (TensorProduct.map LinearMap.id (piOp i g))
  let B : Set (Module.End ℂ ((M₀ ⊗[ℂ] (⨂[ℂ] j, M j)) ⧸ N')) :=
    quotOp N' '' ({f | ∃ g ∈ Op₀, f = TensorProduct.map g LinearMap.id} ∪
      {f | ∃ j, j ≠ i ∧ ∃ h ∈ Op j, f = TensorProduct.map LinearMap.id (piOp j h)})
  have hst0 : ∀ g ∈ Op₀, ∀ z ∈ N', TensorProduct.map g LinearMap.id z ∈ N' :=
    fun g hg => hN'st _ (Or.inl ⟨g, hg, rfl⟩)
  have hst1 : ∀ j, ∀ h ∈ Op j, ∀ z ∈ N', TensorProduct.map LinearMap.id (piOp j h) z ∈ N' :=
    fun j h hh => hN'st _ (Or.inr ⟨piOp j h, ⟨j, h, hh, rfl⟩, rfl⟩)
  have key := GlobalTheory.T.le_ker_of_local_finite_length_to_simple (Op i) Rel K φ act B hlen hmax hK hKst ?_ ?_ ?_ ?_
  · have h0 := key hx
    rw [LinearMap.mem_ker, hφ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
    exact h0
  · intro z hz
    rw [LinearMap.mem_ker, hφ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hRel z hz x₀ y
  · intro g hg
    ext z
    simp only [LinearMap.comp_apply]
    rw [hφ, hφ, quotOp_mk N' _ (hst1 i g hg), TensorProduct.map_tmul, LinearMap.id_apply,
      piOp_tprod_update]
  · intro g hg b hb
    obtain ⟨f, hf, rfl⟩ := hb
    rcases hf with ⟨g₀, hg₀, rfl⟩ | ⟨j, hji, h, hh, rfl⟩
    · rw [quotOp_mul N' _ _ (hst1 i g hg) (hst0 g₀ hg₀), quotOp_mul N' _ _ (hst0 g₀ hg₀) (hst1 i g hg)]
      congr 1
      simp only [Module.End.mul_eq_comp, ← TensorProduct.map_comp, LinearMap.id_comp,
        LinearMap.comp_id]
    · rw [quotOp_mul N' _ _ (hst1 i g hg) (hst1 j h hh), quotOp_mul N' _ _ (hst1 j h hh) (hst1 i g hg)]
      congr 1
      simp only [Module.End.mul_eq_comp, ← TensorProduct.map_comp, LinearMap.id_comp]
      rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, piOp_comm i j hji g h]
  · intro U hU
    have hs : U = (U.comap N'.mkQ).map N'.mkQ :=
      (Submodule.map_comap_eq_of_surjective N'.mkQ_surjective U).symm
    have hle : N' ≤ U.comap N'.mkQ := by
      intro z hz
      rw [Submodule.mem_comap, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N').mpr hz]
      exact U.zero_mem
    have hstab : Stab (tensOps Op₀ (piOps Op)) (U.comap N'.mkQ) := by
      intro f hf z hz
      rw [Submodule.mem_comap] at hz ⊢
      rw [← quotOp_mk N' f (hN'st f hf)]
      apply hU _ _ _ hz
      rcases hf with ⟨g₀, hg₀, rfl⟩ | ⟨p, ⟨j, h, hh, rfl⟩, rfl⟩
      · exact Or.inr ⟨_, Or.inl ⟨g₀, hg₀, rfl⟩, rfl⟩
      · by_cases hji : j = i
        · subst hji
          exact Or.inl ⟨h, hh, rfl⟩
        · exact Or.inr ⟨_, Or.inr ⟨j, hji, h, hh, rfl⟩, rfl⟩
    rcases hN'max _ hstab hle with h | h
    · left
      rw [hs, h, Submodule.mkQ_map_self]
    · right
      rw [hs, h, Submodule.map_top, Submodule.range_mkQ]

end GlobalTheory.TensHead
