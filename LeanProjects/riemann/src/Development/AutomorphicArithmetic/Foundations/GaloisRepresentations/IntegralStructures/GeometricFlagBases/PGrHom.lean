import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.grHom_of :
    GrHom := by
  intro Γ k _ _ d ρ₀ c hinv
  have mem : ∀ (i : ℕ) (v : Fin d → k), v ∈ low k c i ↔ ∀ j, i ≤ c j → v j = 0 :=
    fun _ _ => Iff.rfl
  have hbt : ∀ g, (ρ₀ g : Matrix (Fin d) (Fin d) k).BlockTriangular c := by
    intro g i j hij
    have hv : (Pi.single j (1 : k) : Fin d → k) ∈ low k c (c j + 1) := by
      rw [mem]
      intro j' hj'
      by_cases h : j' = j
      · subst h
        omega
      · simp [Pi.single_apply, h]
    have hw := (mem _ _).1 (hinv (c j + 1) g _ hv) i (by omega)
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hw
  let D : Matrix (Fin d) (Fin d) k → Matrix (Fin d) (Fin d) k :=
    fun M => Matrix.of fun i j => if c i = c j then M i j else 0
  have hD : ∀ M i j, D M i j = if c i = c j then M i j else 0 := fun _ _ _ => rfl
  have hmul : ∀ M N : Matrix (Fin d) (Fin d) k, M.BlockTriangular c → N.BlockTriangular c →
      D (M * N) = D M * D N := by
    intro M N hM hN
    ext i j
    simp only [hD, Matrix.mul_apply]
    split_ifs with hij
    · apply Finset.sum_congr rfl
      intro l _
      by_cases h1 : c i = c l
      · rw [if_pos h1, if_pos (h1 ▸ hij)]
      · rw [if_neg h1, zero_mul]
        rcases lt_or_gt_of_ne h1 with h | h
        · rw [hN (show c j < c l by omega), mul_zero]
        · rw [hM h, zero_mul]
    · symm
      apply Finset.sum_eq_zero
      intro l _
      split_ifs with h1 h2 <;> simp_all
  have hone : D 1 = 1 := by
    ext i j
    simp only [hD, Matrix.one_apply]
    split_ifs <;> simp_all
  have hunit : ∀ g h : Γ, D (ρ₀ g) * D (ρ₀ h) = D (ρ₀ (g * h)) := by
    intro g h
    rw [← hmul _ _ (hbt g) (hbt h), map_mul, Units.val_mul]
  refine ⟨hbt, ⟨{ toFun := fun g => ⟨D (ρ₀ g), D (ρ₀ g⁻¹), ?_, ?_⟩, map_one' := ?_, map_mul' := ?_ }, ?_⟩⟩
  · rw [hunit, mul_inv_cancel, map_one, Units.val_one, hone]
  · rw [hunit, inv_mul_cancel, map_one, Units.val_one, hone]
  · apply Units.ext
    show D (ρ₀ 1) = 1
    rw [map_one, Units.val_one, hone]
  · intro x y
    apply Units.ext
    show D (ρ₀ (x * y)) = D (ρ₀ x) * D (ρ₀ y)
    rw [hunit]
  · intro g i j
    rfl
