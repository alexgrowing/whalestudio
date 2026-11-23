import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LineBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.trace_conj_dotProduct_eq_sum_infinitePlaces :
    ∀ (F : Type) [Field F] [NumberField F] [IsCMField F] (n : ℕ), UpperTheory.Gal.W2.ArchSpan → ∀ (A : Matrix (Fin n) (Fin n) F) (S gr : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) (lam : InfinitePlace F → ℂ), (∀ v, (S v).det ≠ 0) → (∀ v, (S v)⁻¹ᴴ * A.map v.embedding * (S v)⁻¹ = lam v • gr v) → ∀ x y : Fin n → F, ((Algebra.trace ℚ F ((fun i => IsCMField.complexConj F (y i)) ⬝ᵥ (A *ᵥ x)) : ℚ) : ℝ) = ∑ v : InfinitePlace F, 2 * (lam v * hv (gr v) (S v *ᵥ fun i => v.embedding (x i)) (S v *ᵥ fun i => v.embedding (y i))).re := by
  intro F _ _ _ n hA A S gr lam hdet hform x y
  rw [((hA F n).2.2)]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hU : IsUnit (S v).det := isUnit_iff_ne_zero.mpr (hdet v)
  have h1 : (S v)ᴴ * (S v)⁻¹ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hU, Matrix.conjTranspose_one]
  have h2 : (S v)⁻¹ * S v = 1 := Matrix.nonsing_inv_mul _ hU
  have hAmap : A.map v.embedding = (S v)ᴴ * (lam v • gr v) * S v := by
    rw [← hform v]
    calc A.map v.embedding
        = ((S v)ᴴ * (S v)⁻¹ᴴ) * A.map v.embedding * ((S v)⁻¹ * S v) := by
          rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
      _ = (S v)ᴴ * ((S v)⁻¹ᴴ * A.map v.embedding * (S v)⁻¹) * S v := by
          simp only [Matrix.mul_assoc]
  have e1 : v.embedding ((fun i => IsCMField.complexConj F (y i)) ⬝ᵥ (A *ᵥ x))
      = (star fun i => v.embedding (y i)) ⬝ᵥ (A.map v.embedding *ᵥ fun i => v.embedding (x i)) := by
    simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Matrix.map_apply, Pi.star_apply,
      IsCMField.complexEmbedding_complexConj]
    rfl
  have e2 : v.embedding ((fun i => IsCMField.complexConj F (y i)) ⬝ᵥ (A *ᵥ x))
      = lam v * hv (gr v) (S v *ᵥ fun i => v.embedding (x i)) (S v *ᵥ fun i => v.embedding (y i)) := by
    rw [e1, hAmap, hv, Matrix.star_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec (star fun i => v.embedding (y i)) (S v)ᴴ, Matrix.smul_mulVec]
    simp [Matrix.vecMul_conjTranspose, dotProduct_smul]
  rw [e2]
