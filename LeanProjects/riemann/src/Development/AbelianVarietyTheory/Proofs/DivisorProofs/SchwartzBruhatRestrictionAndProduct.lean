import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtendByZeroAdd
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.AdaptEv

namespace GlobalTheory.ThK.AdaptEv

theorem continuous_wittExtendByZero {R : Type} [TopologicalSpace R] [Zero R] {κ ι κ₁ : Type} (eq : κ ≃ ι ⊕ κ₁) :
    Continuous (ext0 (R := R) eq) := by
  refine continuous_pi fun k => ?_
  simp only [ext0]
  rcases eq k with i | j
  · exact continuous_const
  · exact continuous_apply j

theorem isClosedEmbedding_extend_by_zero {R : Type} [TopologicalSpace R] [Zero R] [T1Space R] {κ ι κ₁ : Type}
    (eq : κ ≃ ι ⊕ κ₁) : IsClosedEmbedding (ext0 (R := R) eq) := by
  have hl : Function.LeftInverse (fun (x : κ → R) j => x (eq.symm (Sum.inr j))) (ext0 (R := R) eq) :=
    fun a => funext fun j => ext0_inr eq a j
  refine ⟨hl.isEmbedding (by fun_prop) (continuous_wittExtendByZero eq), ?_⟩
  have : Set.range (ext0 (R := R) eq) = ⋂ i, (fun x : κ → R => x (eq.symm (Sum.inl i))) ⁻¹' {0} := by
    ext x
    simp only [Set.mem_range, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
    refine ⟨fun ⟨a, ha⟩ i => ha ▸ ext0_inl eq a i, fun h => ⟨fun j => x (eq.symm (Sum.inr j)), funext fun k => ?_⟩⟩
    obtain ⟨s, rfl⟩ := eq.symm.surjective k
    rcases s with i | j
    · rw [ext0_inl, h]
    · rw [ext0_inr]
  rw [this]
  exact isClosed_iInter fun i => isClosed_singleton.preimage (continuous_apply _)

def blockHomeo {R : Type} [TopologicalSpace R] {κ ι κ₁ : Type} (eq : κ ≃ ι ⊕ κ₁) :
    (κ → R) ≃ₜ (ι → R) × (κ₁ → R) where
  toFun x := (fun i => x (eq.symm (Sum.inl i)), fun j => x (eq.symm (Sum.inr j)))
  invFun p := fun k => Sum.elim p.1 p.2 (eq k)
  left_inv x := by
    funext k
    obtain ⟨s, rfl⟩ := eq.symm.surjective k
    rcases s with i | j <;> simp
  right_inv p := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by
    refine continuous_pi fun k => ?_
    rcases eq k with i | j
    · exact (continuous_apply i).comp continuous_fst
    · exact (continuous_apply j).comp continuous_snd

theorem sb_restrL_prodVac : ∀ {R : Type} [TopologicalSpace R] [Zero R] [T1Space R] {κ ι κ₁ : Type} [Fintype κ] [Fintype ι] [Fintype κ₁] (eq : κ ≃ ι ⊕ κ₁),
    (∀ g ∈ SB (κ → R), restrL eq g ∈ SB (κ₁ → R)) ∧ ∀ A ∈ SB (ι → R), ∀ φ ∈ SB (κ₁ → R), prodVac eq A φ ∈ SB (κ → R) := by
  intro R _ _ _ κ ι κ₁ _ _ _ eq
  refine ⟨fun g hg => ⟨hg.1.comp_continuous (continuous_wittExtendByZero eq),
    hg.2.comp_isClosedEmbedding (isClosedEmbedding_extend_by_zero eq)⟩, fun A hA φ hφ => ⟨?_, ?_⟩⟩
  · exact (hA.1.comp_continuous (f := fun (x : κ → R) i => x (eq.symm (Sum.inl i))) (by fun_prop)).mul
      (hφ.1.comp_continuous (f := fun (x : κ → R) j => x (eq.symm (Sum.inr j))) (by fun_prop))
  · have h : HasCompactSupport fun p : (ι → R) × (κ₁ → R) => A p.1 * φ p.2 := by
      refine HasCompactSupport.intro' (IsCompact.prod hA.2 hφ.2)
        ((isClosed_tsupport A).prod (isClosed_tsupport φ)) fun p hp => ?_
      rw [Set.mem_prod, not_and_or] at hp
      rcases hp with hp | hp
      · rw [image_eq_zero_of_notMem_tsupport hp, zero_mul]
      · rw [image_eq_zero_of_notMem_tsupport hp, mul_zero]
    exact h.comp_homeomorph (blockHomeo eq)

end GlobalTheory.ThK.AdaptEv
