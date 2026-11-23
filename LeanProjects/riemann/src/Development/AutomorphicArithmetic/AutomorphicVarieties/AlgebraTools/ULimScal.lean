import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UltraDefs

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.ULim.scal_eq :
    ∀ (R ι : Type) [CommRing R] (F : Filter ι) (I : ℕ → Ideal R) (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)],
      (∀ (r : ι → R) (s : R), (∀ j, ∀ᶠ N in F, ∀ x : M N, (r N - s) • x ∈ (I j • ⊤ : Submodule R (M N))) →
        ∀ x : ULim F I M, ULim.scal F I M r x = s • x) ∧
      (∀ s : R, (∀ j, ∀ᶠ N in F, ∀ x : M N, s • x ∈ (I j • ⊤ : Submodule R (M N))) → ∀ x : ULim F I M, s • x = 0) ∧
      (∀ (M' : ι → Type) [∀ i, AddCommGroup (M' i)] [∀ i, Module R (M' i)] (f : ∀ i, M i →ₗ[R] M' i) (g : ∀ i, M' i →ₗ[R] M i) (r : ι → R), (∀ i x, g i (f i x) = r i • x) →
        ∀ x : ULim F I M, ULim.map F (fun _ => le_rfl) g (ULim.map F (I' := I) (fun _ => le_rfl) f x) = ULim.scal F I M r x) := by
  intro R ι _ F I M _ _
  have hs : ∀ (r : ι → R) (p : ∀ i, M i), ULim.scal F I M r (ULim.mk F I M p) = ULim.mk F I M (fun i => r i • p i) := by
    intro r p
    simp only [ULim.scal, ULim.map_mk, LinearMap.smul_apply, LinearMap.id_apply]
  have hc : ∀ (s : R) (p : ∀ i, M i), s • ULim.mk F I M p = ULim.mk F I M (fun i => s • p i) := by
    intro s p
    rw [← map_smul]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro r s h x
    obtain ⟨p, rfl⟩ := ULim.mk_surjective F I M x
    rw [← sub_eq_zero, hs, hc, ← map_sub, ULim.mk_eq_zero]
    intro j
    filter_upwards [h j] with N hN
    simpa [sub_smul] using hN (p N)
  · intro s h x
    obtain ⟨p, rfl⟩ := ULim.mk_surjective F I M x
    rw [hc, ULim.mk_eq_zero]
    intro j
    filter_upwards [h j] with N hN
    exact hN (p N)
  · intro M' _ _ f g r hfg x
    obtain ⟨p, rfl⟩ := ULim.mk_surjective F I M x
    rw [ULim.map_mk, ULim.map_mk, hs]
    simp only [hfg]
