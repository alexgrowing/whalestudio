import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.LatChain

variable {K : Type} [Field K] {N : ℕ}

theorem exists_mul_one_sub_smul {R : Subring K} {h : K} (hh : Small R h) {F : Matrix (Fin N) (Fin N) K}
    (hF : F ∈ R.matrix) : ∃ G ∈ R.matrix, G * (1 - h • F) = 1 := by
  let h' : R := ⟨h, hh.1⟩
  let F' : Matrix (Fin N) (Fin N) R := fun i j => ⟨F i j, hF i j⟩
  have h1 : Ideal.Quotient.mk (Ideal.span {h'}) (1 - h' • F').det = Ideal.Quotient.mk (Ideal.span {h'}) 1 := by
    have h0 : Ideal.Quotient.mk (Ideal.span {h'}) h' = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    have : (Ideal.Quotient.mk (Ideal.span {h'})).mapMatrix (1 - h' • F') = 1 := by
      rw [map_sub, map_one, sub_eq_self]
      ext i j
      simp [h0]
    rw [RingHom.map_det, this, Matrix.det_one, map_one]
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h1)
  obtain ⟨s, hs, hs'⟩ := hh.2 r r.2
  have hu : IsUnit (1 - h' • F').det := by
    refine IsUnit.of_mul_eq_one ⟨s, hs⟩ (Subtype.ext ?_)
    have : (1 - h' • F').det = 1 + h' * r := by rw [mul_comm, hr]; ring
    rw [this]
    exact hs'
  refine ⟨R.subtype.mapMatrix (1 - h' • F')⁻¹, fun i j => ((1 - h' • F')⁻¹ i j).2, ?_⟩
  have e : R.subtype.mapMatrix (1 - h' • F') = 1 - h • F := by
    rw [map_sub, map_one]
    rfl
  rw [← e, ← map_mul, Matrix.nonsing_inv_mul _ hu, map_one]

theorem mul_apply_self_of_upper {A B : Matrix (Fin N) (Fin N) K} (hA : A.BlockTriangular id)
    (hB : B.BlockTriangular id) (i : Fin N) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)
  rcases lt_or_gt_of_ne hj with h | h
  · rw [hA h, zero_mul]
  · rw [hB h, mul_zero]

theorem triMod_inv (K : Type) [Field K] (N : ℕ) (R : Subring K) (h b : K) (A : Matrix (Fin N) (Fin N) K) (d : Fin N → K)
    (hh : Small R h) (hb : b ∈ R) (hA : A.det ≠ 0) (hi : b • A⁻¹ ∈ R.matrix) (H : TriMod R (h * b * b) A d) :
    (∀ i, d i ≠ 0) ∧ TriMod R h A⁻¹ fun i => (d i)⁻¹ := by
  obtain ⟨E, hE, h₁, h₂⟩ := H
  have hF : b • ((b • A⁻¹) * E) ∈ R.matrix := fun i j => R.mul_mem hb (mul_mem hi hE i j)
  obtain ⟨G, hG, hGe⟩ := exists_mul_one_sub_smul hh hF
  have e₁ : (G * A⁻¹) * (A - (h * b * b) • E) = 1 := by
    rw [← hGe, mul_assoc, mul_sub, Matrix.nonsing_inv_mul _ hA.isUnit, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      smul_smul]
  have e₂ : A⁻¹ - h • (-(G * ((b • A⁻¹) * E) * (b • A⁻¹))) = G * A⁻¹ := by
    have : A⁻¹ = G * (1 - h • b • ((b • A⁻¹) * E)) * A⁻¹ := by rw [hGe, one_mul]
    rw [mul_sub, sub_mul, mul_one] at this
    rw [smul_neg, sub_neg_eq_add, ← eq_sub_iff_add_eq]
    refine this.trans ?_
    simp only [Matrix.smul_mul, Matrix.mul_smul]
  have t : (G * A⁻¹).BlockTriangular id := by
    letI := invertibleOfLeftInverse _ _ e₁
    rw [← Matrix.inv_eq_left_inv e₁]
    exact Matrix.blockTriangular_inv_of_blockTriangular h₁
  have e₃ (i) : (G * A⁻¹) i i * d i = 1 := by
    rw [← h₂, ← mul_apply_self_of_upper t h₁, e₁, Matrix.one_apply_eq]
  refine ⟨fun i => right_ne_zero_of_mul_eq_one (e₃ i), -(G * ((b • A⁻¹) * E) * (b • A⁻¹)),
    neg_mem (mul_mem (mul_mem hG (mul_mem hi hE)) hi), ?_, fun i => ?_⟩
  · rwa [e₂]
  · rw [e₂]
    exact eq_inv_of_mul_eq_one_left (e₃ i)

end GlobalTheory.LatChain
