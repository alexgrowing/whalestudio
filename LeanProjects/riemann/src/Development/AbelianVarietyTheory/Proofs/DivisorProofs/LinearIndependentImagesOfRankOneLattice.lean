import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Dets
open NumberField

namespace GlobalTheory

theorem linearIndependent_images_of_rankOne_lattice :
    ∀ {K : Type} [Field K] [NumberField K] {p m n : ℕ} (ell : Submodule (𝓞 K) (Fin m → K))
    (M : Fin p → ((Fin m → K) →ₗ[K] (Fin n → K))) (v : Fin m → K), v ≠ 0 → ∀ (𝔟 : Submodule (𝓞 K) K),
    𝔟 ≠ ⊥ → (∀ e, e ∈ ell ↔ ∃ β ∈ 𝔟, e = β • v) → (∀ a, Function.Injective (M a)) →
    iSupIndep (fun a => Submodule.span K
      ((ell.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) →
    LinearIndependent K (fun a => M a v) := by
  intro K _ _ p m n ell M v hv 𝔟 h𝔟 hell hinj hind
  obtain ⟨β, hβ, hβ0⟩ := (Submodule.ne_bot_iff 𝔟).1 h𝔟
  refine hind.linearIndependent _ (fun a => ?_) (fun a => ?_)
  · have hmem : M a (β • v) ∈ Submodule.span K
        ((ell.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K)) :=
      Submodule.subset_span ⟨β • v, (hell _).2 ⟨β, hβ, rfl⟩, rfl⟩
    have : M a v = β⁻¹ • M a (β • v) := by
      rw [map_smul, smul_smul, inv_mul_cancel₀ hβ0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hmem
  · intro h
    exact hv ((hinj a) (by rw [h, map_zero]))

end GlobalTheory
