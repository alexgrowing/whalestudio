import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange

private theorem UpperTheory.Gal.W2.mul_inv_star_of_triv {S A : Type*} [Ring S] [CommRing A] [Algebra A S]
    (σ : S →+* Sᵐᵒᵖ) (b : S) (x x' : Sˣ) (t t' : Aˣ)
    (hx : (x : S) * b * (σ x).unop = algebraMap A S t)
    (hx' : (x' : S) * b * (σ x').unop = algebraMap A S t') :
    ((x * x'⁻¹ : Sˣ) : S) * (σ ((x * x'⁻¹ : Sˣ) : S)).unop = algebraMap A S ((t * t'⁻¹ : Aˣ) : A) := by
  have key : ∀ u : Sˣ, (σ (u : S)).unop * (σ ((u⁻¹ : Sˣ) : S)).unop = 1 := by
    intro u
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have hb : b = ((x'⁻¹ : Sˣ) : S) * (algebraMap A S t' * (σ ((x'⁻¹ : Sˣ) : S)).unop) := by
    rw [← hx']
    calc b = (((x'⁻¹ : Sˣ) : S) * x') * b * ((σ (x' : S)).unop * (σ ((x'⁻¹ : Sˣ) : S)).unop) := by
          rw [Units.inv_mul, key, one_mul, mul_one]
      _ = _ := by simp only [mul_assoc]
  rw [hb] at hx
  simp only [mul_assoc, Algebra.left_comm] at hx
  simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, mul_assoc]
  calc _ = algebraMap A S ((t'⁻¹ * t' : Aˣ) : A) * ((x : S) * (((x'⁻¹ : Sˣ) : S) *
        ((σ ((x'⁻¹ : Sˣ) : S)).unop * (σ (x : S)).unop))) := by simp
    _ = algebraMap A S ((t'⁻¹ : Aˣ) : A) * algebraMap A S t := by
        rw [Units.val_mul, map_mul, mul_assoc, hx]
    _ = _ := Algebra.commutes _ _

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.adOfWit_of :
    UpperTheory.Gal.W2.AdCore → UpperTheory.Gal.W2.AdOfWit := by
  intro hcore p _ D G L B D' j hpl f nu hw
  obtain ⟨x, c, hxc, hread⟩ := hcore p D G L B.β D' j hpl f nu hw
  obtain ⟨t0, ht0⟩ := B.trivAf.choose_spec
  have hmem : ((trivX B * x⁻¹, t0 * c⁻¹) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) ∈ UPts G.star (AfP p) := by
    rw [UPts, mem_uGroup]
    exact mul_inv_star_of_triv _ _ _ _ _ _ ht0 hxc
  refine ⟨⟨_, hmem⟩, ?_⟩
  have hrd : ∀ w, rd L (trivX B) ⟨_, hmem⟩ w = rd L x 1 w := by
    intro w
    have hy : (((trivX B * x⁻¹)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * (trivX B : AfP p ⊗[ℚ] G.C) = x := by
      rw [← Units.val_mul]
      congr 1
      group
    simp only [rd, inv_one, map_one, Module.End.one_apply]
    rw [← hy, map_mul, Module.End.mul_apply]
    rfl
  intro n hn hcop
  obtain ⟨h1, h2⟩ := hread n hn hcop
  exact ⟨fun w => by rw [hrd]; exact h1 w, fun a => by rw [hrd]; exact h2 a⟩
