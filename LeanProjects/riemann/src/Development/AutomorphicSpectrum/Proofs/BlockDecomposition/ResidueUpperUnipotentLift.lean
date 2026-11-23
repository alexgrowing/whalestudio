import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
open Matrix GlobalTheory.CompanionTheory.Jp

namespace GlobalTheory.CompanionTheory.Jp

theorem tauM_val_blocks {L : Type} [Field L] {n : ℕ} (w : Lˣ) :
    ((tauM (n := n) w : GL (Ix n) L) : Matrix (Ix n) (Ix n) L) =
      fromBlocks 1 0 0 ((w : L) • (1 : Matrix (Fin n) (Fin n) L)) := by
  ext i k
  rcases i with i | i <;> rcases k with k | k <;>
    simp [tauM, pM, scM, Matrix.one_apply, Matrix.diagonal_apply]

theorem twist_low : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
    ∀ x : GL (Ix n) (IsLocalRing.ResidueField O), x.1.toBlocks₁₂ = 0 →
      ∃ j j' : GL (Ix n) O, inL j * tauM w = tauM w * inL j' ∧ resK j' = x := by
  intro O L _ _ _ _ _ _ n ϖ hϖ w hw x hx
  classical
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : IsLocalRing.ResidueField O → O, ∀ a, IsLocalRing.residue O (ℓ a) = a :=
    ⟨Function.surjInv IsLocalRing.residue_surjective, Function.surjInv_eq _⟩
  have hmapℓ : ∀ B : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O),
      (B.map ℓ).map (IsLocalRing.residue O) = B := by
    intro B
    ext i k
    simp [hℓ]
  obtain ⟨A, hA⟩ : ∃ A, A = x.1.toBlocks₁₁.map ℓ := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = x.1.toBlocks₂₁.map ℓ := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = x.1.toBlocks₂₂.map ℓ := ⟨_, rfl⟩
  have hred : (fromBlocks A 0 C D).map (IsLocalRing.residue O) = x.1 := by
    rw [Matrix.fromBlocks_map, hA, hC, hD, hmapℓ, hmapℓ, hmapℓ,
      Matrix.map_zero _ (map_zero _), ← hx, Matrix.fromBlocks_toBlocks]
  have hdet : IsUnit (A.det * D.det) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    have h1 : IsLocalRing.residue O (A.det * D.det) = x.1.det := by
      rw [← Matrix.det_fromBlocks_zero₁₂ A C D, RingHom.map_det, RingHom.mapMatrix_apply, hred]
    rw [h1]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp x.isUnit).ne_zero
  let j' : GL (Ix n) O := Matrix.nonsingInvUnit (fromBlocks A 0 C D)
    (by rw [Matrix.det_fromBlocks_zero₁₂]; exact hdet)
  let j : GL (Ix n) O := Matrix.nonsingInvUnit (fromBlocks A 0 (ϖ • C) D)
    (by rw [Matrix.det_fromBlocks_zero₁₂]; exact hdet)
  refine ⟨j, j', ?_, ?_⟩
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul, tauM_val_blocks]
    show (fromBlocks A 0 (ϖ • C) D).map (algebraMap O L) * _ =
      _ * (fromBlocks A 0 C D).map (algebraMap O L)
    rw [Matrix.fromBlocks_map, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    congr 1
    · simp
    · simp
    · ext i k
      simp [hw, Matrix.map_apply, Matrix.smul_apply]
      rw [Algebra.smul_def]
    · ext i k
      simp [hw]
  · apply Units.ext
    exact hred

end GlobalTheory.CompanionTheory.Jp
