import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAevalEqOfSeparable
open GlobalTheory.UnitLemma Polynomial Matrix

namespace GlobalTheory.InertUnitOrb

theorem stdH_mulVec_of_unitary (K : UQ) (n : ℕ) (γ : Matrix (Fin n) (Fin n) K.E)
    (hγ : (γ.map K.c)ᵀ * γ = 1) (y z : Fin n → K.E) :
    stdH K n (γ *ᵥ y) (γ *ᵥ z) = stdH K n y z := by
  have h1 : ∀ u v : Fin n → K.E, stdH K n u v = u ⬝ᵥ (fun k => K.c (v k)) := fun u v => rfl
  have h2 : (fun k => K.c ((γ *ᵥ z) k)) = (γ.map K.c) *ᵥ (fun k => K.c (z k)) := by
    funext k
    simp [Matrix.mulVec, dotProduct, map_sum]
  rw [h1, h1, h2, dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hγ, one_mulVec]

theorem exists_isModel_of_unitary : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (γ : Matrix (Fin n) (Fin n) K.E), (γ.map K.c)ᵀ * γ = 1 → B.g * B.σ B.g = 1 → B.P.Separable → γ.charpoly = B.P → ∃ (x : B.Aˣ) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B γ x ψ := by
  intro K B n γ hγ hg hsep hchar
  obtain ⟨x, e, h1, h2, h3⟩ := PairClass.exists_herm_model K (Fin n → K.E) (stdH K n)
    (fun x y z => by simp [stdH, add_mul, Finset.sum_add_distrib])
    (fun c x z => by simp [stdH, Finset.mul_sum, mul_assoc])
    (fun x y => by
      simp only [stdH, map_sum, map_mul, K.c_c]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _)
    (fun y hy => by
      funext k
      have := hy (Pi.single k 1)
      rw [stdH, Finset.sum_eq_single k] at this
      · simpa using this
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · simp)
    B (Matrix.toLin' γ) hsep (by rw [Matrix.charpoly_toLin', hchar])
    (Or.inl ⟨hg, fun y z => by
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, stdH_mulVec_of_unitary K n γ hγ]⟩)
  exact ⟨x, e, h1, fun y => by rw [h2, Matrix.toLin'_apply], h3⟩

end GlobalTheory.InertUnitOrb
