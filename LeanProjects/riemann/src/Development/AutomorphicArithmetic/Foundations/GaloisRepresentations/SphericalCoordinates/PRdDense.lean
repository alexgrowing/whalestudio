import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeNsmulEndomorphismPreservesCompletio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmul

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem powerSeries_expansion_image_dense_with_denominator {p : ℕ} [Fact p.Prime] (D : Datum p) (N : ℕ) (hN : 0 < N) (hNp : N.Coprime p)
    (z : AfP p ⊗[ℚ] VQ D) : ∃ (w : VQ D) (e : AfP p ⊗[ℚ] VQ D), e ∈ LaHat D ∧
      z = (1 : AfP p) ⊗ₜ[ℚ] w + N • e := by
  obtain ⟨t, ht0, htc, ht⟩ := DenEnd.exists_coprime_nsmul_mem D z
  obtain ⟨x, e, he, hx⟩ := exists_inAf_add_nsmul_of_mem_laHat p D (t * N) (Nat.mul_pos ht0 hN)
    (Nat.Coprime.mul_left htc hNp) (t • z) ht
  have ht' : (t : ℚ) ≠ 0 := by exact_mod_cast ht0.ne'
  refine ⟨(t : ℚ)⁻¹ • ((1 : ℚ) ⊗ₜ[ℤ] x), e, he, ?_⟩
  have h1 : t • ((1 : AfP p) ⊗ₜ[ℚ] ((t : ℚ)⁻¹ • ((1 : ℚ) ⊗ₜ[ℤ] x))) = inAf D x := by
    rw [inAf, ← Nat.cast_smul_eq_nsmul ℚ, ← TensorProduct.tmul_smul, smul_smul, mul_inv_cancel₀ ht', one_smul]
  have h2 : t • z = t • ((1 : AfP p) ⊗ₜ[ℚ] ((t : ℚ)⁻¹ • ((1 : ℚ) ⊗ₜ[ℤ] x)) + N • e) := by
    rw [hx, smul_add, h1, smul_smul]
  rw [← Nat.cast_smul_eq_nsmul ℚ t, ← Nat.cast_smul_eq_nsmul ℚ t] at h2
  exact smul_right_injective _ ht' h2

theorem UpperTheory.Gal.W2.rdDense_of :
    UpperTheory.Gal.W2.RdDense := by
  intro p _ D G L x h₁ n hn z
  let T : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) :=
    L.actG h₁⁻¹ * actOn L.rep (AfP p) (x : AfP p ⊗[ℚ] G.C)
  let S : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) :=
    actOn L.rep (AfP p) ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * L.actG h₁
  have hTS : T * S = 1 := by
    have e1 : actOn L.rep (AfP p) (x : AfP p ⊗[ℚ] G.C) *
        actOn L.rep (AfP p) ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have e2 : L.actG h₁⁻¹ * L.actG h₁ = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    change (L.actG h₁⁻¹ * actOn L.rep (AfP p) (x : AfP p ⊗[ℚ] G.C)) *
      (actOn L.rep (AfP p) ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * L.actG h₁) = 1
    rw [_root_.mul_assoc, ← _root_.mul_assoc (actOn L.rep (AfP p) (x : AfP p ⊗[ℚ] G.C)), e1, _root_.one_mul, e2]
  obtain ⟨m, hm0, hmc, hm⟩ := DenEnd.exists_coprime_nsmul_map_mem p D T
  obtain ⟨k, n', hn', hnn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p (Fact.out : p.Prime).ne_one
  have hn0 : 0 < n' := Nat.pos_of_ne_zero fun h => hn' (h ▸ dvd_zero p)
  have hnc : n'.Coprime p := ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hn').symm
  obtain ⟨w, e, he, hz⟩ := powerSeries_expansion_image_dense_with_denominator D (n' * m) (Nat.mul_pos hn0 hm0) (Nat.Coprime.mul_left hnc hmc) (S z)
  have hint : IsIntAf (algebraMap ℚ (AfP p) ((p : ℚ)⁻¹ ^ k)) := fun u => by
    rw [map_pow, map_pow]; exact pow_mem (DenEnd.isIntAf_inv u) k
  have hz2 : z = T (S z) := by
    rw [← Module.End.mul_apply, hTS]; rfl
  have hr : rd L x h₁ w = T ((1 : AfP p) ⊗ₜ[ℚ] w) := rfl
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine ⟨w, algebraMap ℚ (AfP p) ((p : ℚ)⁻¹ ^ k) • (m • T e), DenEnd.smul_mem D hint (hm e he), ?_⟩
  rw [hr, hz2, hz, map_add, map_nsmul]
  congr 1
  rw [algebraMap_smul, hnn]
  simp only [← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  congr 1
  have hpk : (p : ℚ) ^ k * ((p : ℚ)⁻¹) ^ k = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hp, one_pow]
  push_cast
  linear_combination (-((n' : ℚ) * m)) * hpk
