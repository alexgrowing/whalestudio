import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LineBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.span_real_matrix_mulVec_infinitePlace_embedding_eq_top :
    ∀ (F : Type) [Field F] [NumberField F] [IsCMField F] (n : ℕ), UpperTheory.Gal.W2.ArchSpan → ∀ S : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ, (∀ v, (S v).det ≠ 0) → Submodule.span ℝ (Set.range fun (x : Fin n → F) (v : InfinitePlace F) => S v *ᵥ fun i => v.embedding (x i)) = ⊤ := by
  intro F _ _ _ n hA S hS
  let Ph : (InfinitePlace F → Fin n → ℂ) →ₗ[ℝ] (InfinitePlace F → Fin n → ℂ) :=
    { toFun := fun x v => S v *ᵥ x v
      map_add' := fun x y => by
        funext v
        simp [Matrix.mulVec_add]
      map_smul' := fun c x => by
        funext v
        simp [Matrix.mulVec_smul] }
  have hsurj : Function.Surjective Ph := by
    intro y
    refine ⟨fun v => (S v)⁻¹ *ᵥ y v, ?_⟩
    funext v
    have hu : IsUnit (S v).det := isUnit_iff_ne_zero.2 (hS v)
    change S v *ᵥ ((S v)⁻¹ *ᵥ y v) = y v
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have h := congrArg (Submodule.map Ph) (hA F n).1
  rw [Submodule.map_span, Submodule.map_top, LinearMap.range_eq_top.2 hsurj, ← Set.range_comp] at h
  exact h
