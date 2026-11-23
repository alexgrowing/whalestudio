import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
open TensorProduct

theorem GlobalTheory.tensor_fraction_injective_of_injective
    (R R₁ B K L : Type) [CommRing R] [CommRing R₁] [CommRing B] [Field K] [Field L] [Algebra R R₁]
    [Algebra R B] [Algebra R K] [Algebra B K] [IsScalarTower R B K] [IsFractionRing B K]
    (θ : K →+* L) (c : R₁ →+* L) (β : B ⊗[R] R₁ →+ L) (hβ : Function.Injective β)
    (hβt : ∀ b r, β (b ⊗ₜ[R] r) = θ (algebraMap B K b) * c r)
    (n : ℕ) (u : Fin n → K) (r : Fin n → R₁) (h : ∑ j, c (r j) * θ (u j) = 0) :
    ∑ j, u j ⊗ₜ[R] r j = 0 := by
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors B) (Finset.univ : Finset (Fin n)) u
  choose x hx using fun j => hs j (Finset.mem_univ j)

  have hx' : ∀ j, algebraMap B K (x j) = algebraMap B K (s : B) * u j := by
    intro j; rw [hx j, Algebra.smul_def]
  have h0 : ∑ j, x j ⊗ₜ[R] r j = 0 := by
    apply hβ
    rw [map_sum, map_zero]
    simp only [hβt, hx', map_mul]
    calc ∑ j, θ (algebraMap B K (s : B)) * θ (u j) * c (r j)
        = θ (algebraMap B K (s : B)) * ∑ j, c (r j) * θ (u j) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [h, mul_zero]
  have h1 := congrArg ((IsScalarTower.toAlgHom R B K).toLinearMap.rTensor R₁) h0
  simp only [map_sum, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
    IsScalarTower.coe_toAlgHom', map_zero] at h1
  have h2 : (algebraMap B K (s : B)) • ∑ j, u j ⊗ₜ[R] r j = 0 := by
    rw [Finset.smul_sum]
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, hx'] using h1
  have hne : algebraMap B K (s : B) ≠ 0 :=
    (IsLocalization.map_units K s).ne_zero
  have := congrArg (fun z => (algebraMap B K (s : B))⁻¹ • z) h2
  simp only [smul_zero] at this
  rwa [inv_smul_smul₀ hne] at this
