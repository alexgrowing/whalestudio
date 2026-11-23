import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ValuationLeIffExistsSmulMem
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLetterIntegralOfLocalGeneratorStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem valuation_det_le_one_of_entries {K G J : Type} [Field K] [LinearOrderedCommGroupWithZero G]
    [Fintype J] [DecidableEq J] (v : Valuation K G) (N : Matrix J J K) (h : ∀ i j, v (N i j) ≤ 1) :
    v N.det ≤ 1 := by
  rw [Matrix.det_apply]
  refine v.map_sum_le fun σ _ => ?_
  have hp : v (∏ i, N (σ i) i) ≤ 1 := by
    rw [map_prod]
    exact Finset.prod_le_one' fun i _ => h _ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul]; exact hp
  · rw [hs, Units.neg_smul, one_smul, Valuation.map_neg]; exact hp

theorem valuation_prod_mul_det_le {K G J : Type} [Field K] [LinearOrderedCommGroupWithZero G]
    [Fintype J] [DecidableEq J] (v : Valuation K G) (U M : Matrix J J K) (c : J → K) (hM : M.det ≠ 0)
    (h : ∀ k m, v (Matrix.vecMul (c k • U k) M⁻¹ m) ≤ 1) :
    v ((∏ k, c k) * U.det) ≤ v M.det := by
  have hN : v (Matrix.diagonal c * U * M⁻¹).det ≤ 1 := by
    refine valuation_det_le_one_of_entries v _ fun k m => ?_
    have hk : (Matrix.diagonal c * U) k = c k • U k := by
      funext j
      simp [Matrix.diagonal_mul]
    have : (Matrix.diagonal c * U * M⁻¹) k m = Matrix.vecMul (c k • U k) M⁻¹ m := by
      rw [← hk]; rfl
    rw [this]; exact h k m
  have hvM : v M.det ≠ 0 := (Valuation.ne_zero_iff v).2 hM
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
    map_mul, map_inv₀, ← div_eq_mul_inv, div_le_one₀ (zero_lt_iff.2 hvM)] at hN
  exact hN

theorem letters_det_valuation_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (l : Level H) (c : Coeff l) (nΨ n' f : ℕ) (o : LamObj c nΨ n') (La : ℝ), LamObjGood o f La → ∀ L : LamLetters o, L.IsGood → ∀ (p : HeightOneSpectrum (𝓞 o.K₁)) (cd : o.K₁) (cl : Fin o.xB.P.g → o.K₁), IsLocGen p cd o.LamL.I → (∀ k, IsLocGen p (cl k) (L.ℓ k).I) → p.valuation o.K₁ ((∏ k, cl k) * L.U.det) ≤ p.valuation o.K₁ cd := by
  intro E _ _ _ _ H l c nΨ n' f o La ho L hL p cd cl hcd hcl
  obtain ⟨M, hM, hdet⟩ := ho.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 p
  have hv : p.valuation o.K₁ M.det = p.valuation o.K₁ cd := by
    rw [(isLocGen_iff_valuation_eq p _ _).1 hdet, (isLocGen_iff_valuation_eq p _ _).1 hcd]
  rw [← hv]
  exact valuation_prod_mul_det_le _ L.U M cl hdet.1 fun k m =>
    GlobalTheory.T.lieLetter_integral_of_local_generator E H l c nΨ n' f o La ho L hL p M hM k (cl k) (hcl k) m

end GlobalTheory.LamF
