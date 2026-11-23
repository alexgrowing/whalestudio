import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
import Formalism.PadicSubsetSums.StableGradedCounts.ZBrauerNesbitt
import Mathlib.RepresentationTheory.Semisimple

open Polynomial Matrix UpperTheory.V.W

private noncomputable def UpperTheory.V.AlgebraTools.Det.bnRep_lin {n : ℕ} {K G : Type} [Field K] [Group G]
    (ρ : G →* Matrix (Fin n) (Fin n) K) : Representation K G (Fin n → K) where
  toFun g := Matrix.toLin' (ρ g)
  map_one' := by rw [map_one, Matrix.toLin'_one]; rfl
  map_mul' g h := by rw [map_mul, Matrix.toLin'_mul]; rfl

private theorem UpperTheory.V.AlgebraTools.Det.bnRep_ss {n : ℕ} {K G : Type} [Field K] [Group G]
    (ρ : G →* Matrix (Fin n) (Fin n) K)
    (h : ∀ W : Submodule K (Fin n → K), (∀ g, ∀ v ∈ W, ρ g *ᵥ v ∈ W) →
      ∃ W', (∀ g, ∀ v ∈ W', ρ g *ᵥ v ∈ W') ∧ IsCompl W W') :
    IsSemisimpleModule (MonoidAlgebra K G) (UpperTheory.V.AlgebraTools.Det.bnRep_lin ρ).asModule := by
  rw [← Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  refine ⟨fun W => ?_⟩
  obtain ⟨W', hW', hc⟩ := h W.toSubmodule (fun g v hv => W.apply_mem_toSubmodule g hv)
  refine ⟨⟨W', fun g v hv => hW' g v hv⟩, ?_, ?_⟩
  · rw [disjoint_iff]
    exact Subrepresentation.toSubmodule_injective hc.inf_eq_bot
  · rw [codisjoint_iff]
    exact Subrepresentation.toSubmodule_injective hc.sup_eq_top

theorem UpperTheory.V.AlgebraTools.Det.bnRep :
    ∀ {n : ℕ} {K G : Type} [Field K] [Group G] (ρ ρ' : G →* Matrix (Fin n) (Fin n) K),
    (∀ W : Submodule K (Fin n → K), (∀ g, ∀ v ∈ W, ρ g *ᵥ v ∈ W) → ∃ W', (∀ g, ∀ v ∈ W', ρ g *ᵥ v ∈ W') ∧ IsCompl W W') →
    (∀ W : Submodule K (Fin n → K), (∀ g, ∀ v ∈ W, ρ' g *ᵥ v ∈ W) → ∃ W', (∀ g, ∀ v ∈ W', ρ' g *ᵥ v ∈ W') ∧ IsCompl W W') →
    (∀ g, (ρ g).charpoly = (ρ' g).charpoly) → ∃ P : GL (Fin n) K, ∀ g, (P : Matrix (Fin n) (Fin n) K) * ρ' g = ρ g * P := by
  intro n K G _ _ ρ ρ' h h' hc
  obtain ⟨e, he⟩ := Formalism.IrreducibleCountingLemmas.Z.brauer_nesbitt K G (Fin n → K) (Fin n → K)
    (UpperTheory.V.AlgebraTools.Det.bnRep_lin ρ') (UpperTheory.V.AlgebraTools.Det.bnRep_lin ρ)
    (UpperTheory.V.AlgebraTools.Det.bnRep_ss ρ' h') (UpperTheory.V.AlgebraTools.Det.bnRep_ss ρ h) (fun g => by
      show (Matrix.toLin' (ρ' g)).charpoly = (Matrix.toLin' (ρ g)).charpoly
      rw [Matrix.charpoly_toLin', Matrix.charpoly_toLin']
      exact (hc g).symm)
  have h1 : LinearMap.toMatrix' (e.symm : (Fin n → K) →ₗ[K] (Fin n → K)) *
      LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K)) = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    simp
  have h2 : LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K)) *
      LinearMap.toMatrix' (e.symm : (Fin n → K) →ₗ[K] (Fin n → K)) = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    simp
  refine ⟨⟨_, _, h2, h1⟩, fun g => ?_⟩
  show LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K)) * ρ' g =
    ρ g * LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K))
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  exact he g
