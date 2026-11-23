import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.Peel

theorem length_eq_inf_ker_add_map {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (C : Submodule R M) :
    Module.length R ↥C = Module.length R ↥(C ⊓ LinearMap.ker f) + Module.length R ↥(C.map f) := by
  refine Module.length_eq_add_of_exact (Submodule.inclusion (inf_le_left : C ⊓ LinearMap.ker f ≤ C))
    (f.submoduleMap C) (Submodule.inclusion_injective _) (f.submoduleMap_surjective C) ?_
  intro y
  constructor
  · intro hy
    have hy' : f y = 0 := by
      simpa [LinearMap.submoduleMap_coe_apply] using congrArg Subtype.val hy
    exact ⟨⟨y.1, y.2, hy'⟩, rfl⟩
  · rintro ⟨z, rfl⟩
    ext
    simpa [LinearMap.submoduleMap_coe_apply] using z.2.2

theorem exists_le_map_eq_bot {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {N : ι → Type*} [∀ q, AddCommGroup (N q)] [∀ q, Module R (N q)] (f : ∀ q, M →ₗ[R] N q)
    (C : Submodule R M) (Q : Finset ι) :
    ∃ C' : Submodule R M, C' ≤ C ∧ (∀ q ∈ Q, C'.map (f q) = ⊥) ∧
      Module.length R ↥C ≤ Module.length R ↥C' + ∑ q ∈ Q, Module.length R ↥(C.map (f q)) := by
  classical
  induction Q using Finset.induction_on with
  | empty => exact ⟨C, le_rfl, by simp, by simp⟩
  | insert q Q hq ih =>
    obtain ⟨C₀, hC₀, hmap, hlen⟩ := ih
    refine ⟨C₀ ⊓ LinearMap.ker (f q), inf_le_left.trans hC₀, ?_, ?_⟩
    · intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · rw [eq_bot_iff]
        rintro _ ⟨x, hx, rfl⟩
        exact hx.2
      · rw [eq_bot_iff, ← hmap p hp]
        exact Submodule.map_mono inf_le_left
    · have hsplit := length_eq_inf_ker_add_map (f q) C₀
      have hle : Module.length R ↥(C₀.map (f q)) ≤ Module.length R ↥(C.map (f q)) :=
        Module.length_le_of_injective _ (Submodule.inclusion_injective (Submodule.map_mono hC₀))
      rw [Finset.sum_insert hq]
      calc Module.length R ↥C ≤ Module.length R ↥C₀ + ∑ p ∈ Q, Module.length R ↥(C.map (f p)) := hlen
        _ = Module.length R ↥(C₀ ⊓ LinearMap.ker (f q)) + Module.length R ↥(C₀.map (f q)) +
              ∑ p ∈ Q, Module.length R ↥(C.map (f p)) := by rw [← hsplit]
        _ ≤ Module.length R ↥(C₀ ⊓ LinearMap.ker (f q)) + Module.length R ↥(C.map (f q)) +
              ∑ p ∈ Q, Module.length R ↥(C.map (f p)) := by gcongr
        _ = _ := by rw [add_assoc]

theorem main : ∀ (D : D7) (i : D.nd.Loc) (k : ℕ) (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k)) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))), ∃ C' : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k), C' ≤ C ∧ (∀ q ∈ Q, resIne i C' q = ⊥) ∧ Module.length (D.nd.O i) ↥C ≤ Module.length (D.nd.O i) ↥C' + ∑ q ∈ Q, Module.length (D.nd.O i) ↥(resIne i C q) := by
  intro D i k C Q
  exact exists_le_map_eq_bot
    (fun q => LinearMap.funLeft (D.nd.O i) (KOG (D.nd.O i) k)
      (Subtype.val : ↥(Ine (F := D.host.E) (D.nd.plOm.1 q)) → GE D.nd)) C Q

end GlobalTheory.Cut.Peel
