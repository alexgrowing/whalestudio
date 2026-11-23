import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BrauerNesbittExistsEquivOfCharpolyEqBindersStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyMonoidAlgebraLiftEqOfCharpolyEqStatement
open scoped BigOperators

namespace GlobalTheory.BrauerNesbittMatrix

def colRep {k G : Type} [Field k] [Monoid G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) k) :
    Representation k G (Fin n → k) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] Module.End k (Fin n → k)).toAlgHom.toRingHom.toMonoidHom.comp ρ

theorem colRep_apply {k G : Type} [Field k] [Monoid G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) k) (g : G) :
    colRep ρ g = Matrix.toLin' (ρ g) := rfl

theorem colRep_asAlgebraHom {k G : Type} [Field k] [Monoid G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) k)
    (a : MonoidAlgebra k G) :
    (colRep ρ).asAlgebraHom a = Matrix.toLin' (MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) G ρ a) := by
  have : (colRep ρ).asAlgebraHom =
      (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] Module.End k (Fin n → k)).toAlgHom.comp
        (MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) G ρ) := by
    apply MonoidAlgebra.algHom_ext
    · intro g
      simp [Representation.asAlgebraHom_single, colRep_apply]
      rfl
    · exact Subsingleton.elim _ _
  rw [this]
  rfl

theorem colRep_semisimple {k G : Type} [Field k] [Monoid G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) k)
    (h : ∀ W : Submodule k (Fin n → k), (∀ g, ∀ v ∈ W, (ρ g).mulVec v ∈ W) →
      ∃ W', IsCompl W W' ∧ ∀ g, ∀ v ∈ W', (ρ g).mulVec v ∈ W') :
    (colRep ρ).IsSemisimpleRepresentation := by
  refine ⟨fun P => ?_⟩
  obtain ⟨W', h2, h1⟩ := h P.toSubmodule fun g v hv => P.apply_mem_toSubmodule g hv
  refine ⟨⟨W', fun g v hv => h1 g v hv⟩, ?_⟩
  rw [isCompl_iff, disjoint_iff, codisjoint_iff,
    ← Subrepresentation.toSubmodule_injective.eq_iff, ← Subrepresentation.toSubmodule_injective.eq_iff]
  rw [isCompl_iff, disjoint_iff, codisjoint_iff] at h2
  exact h2

theorem main : ∀ {k G : Type} [Field k] [Group G] (n : ℕ) (ρ σ : G →* Matrix (Fin n) (Fin n) k), (∀ W : Submodule k (Fin n → k), (∀ g, ∀ v ∈ W, (ρ g).mulVec v ∈ W) → ∃ W', IsCompl W W' ∧ ∀ g, ∀ v ∈ W', (ρ g).mulVec v ∈ W') → (∀ W : Submodule k (Fin n → k), (∀ g, ∀ v ∈ W, (σ g).mulVec v ∈ W) → ∃ W', IsCompl W W' ∧ ∀ g, ∀ v ∈ W', (σ g).mulVec v ∈ W') → (∀ g, (ρ g).charpoly = (σ g).charpoly) → ∃ P : GL (Fin n) k, ∀ g, (P : Matrix (Fin n) (Fin n) k) * ρ g = σ g * P := by
  intro k G _ _ n ρ σ hρ hσ hc
  obtain ⟨e, he⟩ := GlobalTheory.T.brauerNesbitt_exists_equiv_of_charpoly_eq' (colRep ρ) (colRep σ) (colRep_semisimple ρ hρ) (colRep_semisimple σ hσ)
    fun a => by
      rw [colRep_asAlgebraHom, colRep_asAlgebraHom, Matrix.charpoly_toLin', Matrix.charpoly_toLin']
      exact GlobalTheory.T.charpoly_monoidAlgebraLift_eq_of_charpoly_eq n ρ σ hc a
  let P : GL (Fin n) k :=
    ⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap,
      by rw [← LinearMap.toMatrix'_comp]; simp,
      by rw [← LinearMap.toMatrix'_comp]; simp⟩
  refine ⟨P, fun g => ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
  have hh : Matrix.toLin' (P : Matrix (Fin n) (Fin n) k) = e.toLinearMap := Matrix.toLin'_toMatrix' _
  rw [hh]
  refine LinearMap.ext fun v => ?_
  have := he g v
  rw [colRep_apply, colRep_apply] at this
  exact this

end GlobalTheory.BrauerNesbittMatrix
