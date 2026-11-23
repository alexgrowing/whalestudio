import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepresentativesQuotientRangeMulVecLin
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.HasSumLocallyUniformlyOnIteratedFDerivRiemannThe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.GenMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.SemistableReduction.ShareDetA

open Complex Matrix
open scoped Real

noncomputable section

namespace GlobalTheory

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a b c d : Matrix ι ι ℤ}

theorem tsum_eq_sum_tsum_add_mulVec (hd : d.det ≠ 0) {κ : Type*} [Fintype κ] (r : κ → ι → ℤ)
    (hr : Function.Bijective fun k =>
      (Submodule.Quotient.mk (r k) : (ι → ℤ) ⧸ LinearMap.range d.mulVecLin))
    {f : (ι → ℤ) → ℂ} (hf : Summable f) :
    ∑' n, f n = ∑ k, ∑' m, f (r k + d *ᵥ m) := by
  have hb : Function.Bijective fun p : κ × (ι → ℤ) => r p.1 + d *ᵥ p.2 := by
    refine ⟨?_, fun n => ?_⟩
    · rintro ⟨k, m⟩ ⟨k', m'⟩ h
      simp only at h
      obtain rfl : k = k' := hr.1 ((Submodule.Quotient.eq _).2 ⟨m' - m, by
        rw [mulVecLin_apply, mulVec_sub, sub_eq_sub_iff_add_eq_add, add_comm, ← h, add_comm]⟩)
      have h1 : d *ᵥ (m - m') = 0 := by rw [mulVec_sub, add_left_cancel h, sub_self]
      rw [sub_eq_zero.1 (eq_zero_of_mulVec_eq_zero hd h1)]
    · obtain ⟨k, hk⟩ := hr.2 (Submodule.Quotient.mk n)
      obtain ⟨m, hm⟩ := (Submodule.Quotient.eq _).1 hk.symm
      exact ⟨(k, m), by simp only [← mulVecLin_apply, hm, add_sub_cancel]⟩
  rw [← (Equiv.ofBijective _ hb).tsum_eq]
  exact ((Equiv.ofBijective _ hb).summable_iff.2 hf).tsum_prod.trans (tsum_fintype _)

omit [DecidableEq ι] in

theorem intCast_mulVec_complex (d : Matrix ι ι ℤ) (x : ι → ℤ) :
    (fun i => ((d *ᵥ x) i : ℂ)) = d.map ((↑) : ℤ → ℂ) *ᵥ fun i => (x i : ℂ) := by
  ext i
  simp [mulVec, dotProduct]

omit [DecidableEq ι] in

theorem intCast_dotProduct_complex (x y : ι → ℤ) :
    ((x ⬝ᵥ y : ℤ) : ℂ) = (fun i => (x i : ℂ)) ⬝ᵥ fun i => (y i : ℂ) := by
  simp [dotProduct]

theorem symplectic_fromBlocks_relations {R : Type*} [CommRing R] {a b c d : Matrix ι ι R}
    (h : fromBlocks a b c d ∈ symplecticGroup ι R) :
    aᵀ * c = cᵀ * a ∧ aᵀ * d - cᵀ * b = 1 ∧ dᵀ * b = bᵀ * d ∧ c * dᵀ = d * cᵀ ∧
      d * aᵀ - c * bᵀ = 1 := by
  have h' := h
  rw [SymplecticGroup.mem_iff', J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_inj] at h
  rw [SymplecticGroup.mem_iff, J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_inj] at h'
  obtain ⟨h1, h2, -, h3⟩ := h
  obtain ⟨-, -, h4, h5⟩ := h'
  simp only [Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero, Matrix.mul_neg,
    Matrix.neg_mul] at h1 h2 h3 h4 h5
  refine ⟨(add_neg_eq_zero.1 h1).symm, ?_, add_neg_eq_zero.1 h3, (add_neg_eq_zero.1 h5).symm, ?_⟩
  · rw [← neg_inj, ← h2]
    abel
  · rw [← h4]
    abel

theorem fromBlocks_map_intCast_mem_symplecticGroup (R : Type*) [CommRing R]
    (h : fromBlocks a b c d ∈ symplecticGroup ι ℤ) :
    fromBlocks (a.map ((↑) : ℤ → R)) (b.map (↑)) (c.map (↑)) (d.map (↑)) ∈
      symplecticGroup ι R := by
  rw [SymplecticGroup.mem_iff] at h ⊢
  have := congrArg (Int.castRingHom R).mapMatrix h
  rw [map_mul, map_mul] at this
  simp only [RingHom.mapMatrix_apply, Matrix.map_J, transpose_map, fromBlocks_map] at this
  exact this

theorem symplectic_fromBlocks_inv_relations {R : Type*} [CommRing R] {a b c d : Matrix ι ι R}
    (h : fromBlocks a b c d ∈ symplecticGroup ι R) (hd : IsUnit d.det) :
    (b * d⁻¹).IsSymm ∧ (d⁻¹ * c).IsSymm ∧ cᵀ * (b * d⁻¹) = aᵀ - d⁻¹ := by
  obtain ⟨-, h2, h3, h4, -⟩ := symplectic_fromBlocks_relations h
  have hd' := isUnit_det_transpose _ hd
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.IsSymm, transpose_mul, transpose_nonsing_inv, ← mul_nonsing_inv_cancel_right d bᵀ hd,
      ← h3, Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hd']
  · rw [Matrix.IsSymm, transpose_mul, transpose_nonsing_inv, ← nonsing_inv_mul_cancel_left d cᵀ hd,
      ← h4, Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hd']
  · rw [← Matrix.mul_assoc, show cᵀ * b = aᵀ * d - 1 by rw [← h2]; abel, Matrix.sub_mul,
      mul_nonsing_inv_cancel_right _ _ hd, Matrix.one_mul]

theorem isUnit_det_map_intCast (K : Type*) [Field K] [CharZero K] (hd : d.det ≠ 0) :
    IsUnit (d.map ((↑) : ℤ → K)).det := by
  rw [← Int.cast_det]
  simpa using hd

theorem sum_exp_pair_mul_exp (h : fromBlocks a b c d ∈ symplecticGroup ι ℤ) (hd : d.det ≠ 0)
    (hb : ∀ μ, Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ)) (hc : ∀ μ, Even (μ ⬝ᵥ (aᵀ * c) *ᵥ μ))
    {κ : Type*} [Fintype κ] (r : κ → ι → ℤ)
    (hr : Function.Bijective fun k =>
      (Submodule.Quotient.mk (r k) : (ι → ℤ) ⧸ LinearMap.range d.mulVecLin)) (m : ι → ℤ) :
    ∑ k, cexp (π * I * ((fun i => (r k i : ℂ)) ⬝ᵥ
        (b.map ((↑) : ℤ → ℂ) * (d.map ((↑) : ℤ → ℂ))⁻¹) *ᵥ fun i => (r k i : ℂ))) *
      cexp (2 * π * I * ((fun i => (m i : ℂ)) ⬝ᵥ
        (d.map ((↑) : ℤ → ℂ))⁻¹ *ᵥ fun i => (r k i : ℂ))) =
    (∑ k, cexp (π * I * ((fun i => (r k i : ℂ)) ⬝ᵥ
        (b.map ((↑) : ℤ → ℂ) * (d.map ((↑) : ℤ → ℂ))⁻¹) *ᵥ fun i => (r k i : ℂ)))) *
      cexp (π * I * ((fun i => (m i : ℂ)) ⬝ᵥ
        ((d.map ((↑) : ℤ → ℂ))⁻¹ * c.map ((↑) : ℤ → ℂ)) *ᵥ fun i => (m i : ℂ))) := by
  have hs := (symm_coprime_of_mem_symplecticGroup h).1
  obtain ⟨h1, -, h3⟩ := symplectic_fromBlocks_inv_relations
    (fromBlocks_map_intCast_mem_symplecticGroup ℂ h) (isUnit_det_map_intCast ℂ hd)
  let := Fintype.ofBijective _ hr
  set Φ := fun x => ratCircleChar (pairQuadraticForm hd hs hb x) with hΦ
  have e1 : ∑ k, Φ (Submodule.Quotient.mk (r k)) =
      ∑ k, Φ (Submodule.Quotient.mk (r k - c *ᵥ m)) := by
    rw [Fintype.sum_bijective _ hr _ Φ fun _ => rfl]
    exact (Fintype.sum_bijective _
      ((Equiv.subRight (Submodule.Quotient.mk (c *ᵥ m))).bijective.comp hr) _ Φ fun _ => rfl).symm
  simp only [hΦ, ratCircleChar_pairQuadraticForm_mk] at e1
  rw [e1, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  obtain ⟨t, ht⟩ := hc m
  have ht' := congrArg ((↑) : ℤ → ℂ) ht
  rw [← mulVec_mulVec, intCast_dotProduct_complex, intCast_mulVec_complex, intCast_mulVec_complex,
    transpose_map] at ht'
  have hu := intCast_dotProduct_complex m (aᵀ *ᵥ r k)
  rw [intCast_mulVec_complex, transpose_map] at hu
  have e2 : (fun i => ((r k - c *ᵥ m) i : ℂ)) =
      (fun i => (r k i : ℂ)) - c.map ((↑) : ℤ → ℂ) *ᵥ fun i => (m i : ℂ) := by
    rw [← intCast_mulVec_complex]
    ext i
    simp
  have e3 (v : ι → ℂ) : (c.map ((↑) : ℤ → ℂ) *ᵥ fun i => (m i : ℂ)) ⬝ᵥ
      (b.map ((↑) : ℤ → ℂ) * (d.map ((↑) : ℤ → ℂ))⁻¹) *ᵥ v =
      (fun i => (m i : ℂ)) ⬝ᵥ (a.map ((↑) : ℤ → ℂ))ᵀ *ᵥ v -
        (fun i => (m i : ℂ)) ⬝ᵥ (d.map ((↑) : ℤ → ℂ))⁻¹ *ᵥ v := by
    rw [← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, h3, sub_mulVec, dotProduct_sub]
  rw [← Complex.exp_add, ← Complex.exp_add, e2, mulVec_sub, sub_dotProduct, dotProduct_sub,
    dotProduct_sub, dotProduct_mulVec_comm_of_isSymm h1 _ (c.map _ *ᵥ _), e3, e3, ← hu, ht',
    ← mulVec_mulVec (fun i => (m i : ℂ))]
  refine Complex.exp_eq_exp_iff_exists_int.2 ⟨m ⬝ᵥ aᵀ *ᵥ r k - t, ?_⟩
  push_cast
  ring

theorem IsSiegel.neg_inv_add_inv_mul {τ : Matrix ι ι ℂ} (hτ : IsSiegel τ)
    (h : fromBlocks a b c d ∈ symplecticGroup ι ℤ) (hd : d.det ≠ 0) :
    IsSiegel (-(τ⁻¹ + (d.map ((↑) : ℤ → ℂ))⁻¹ * c.map ((↑) : ℤ → ℂ))) := by
  have hu := isUnit_det_map_intCast ℝ hd
  obtain ⟨-, h2, -⟩ := symplectic_fromBlocks_inv_relations
    (fromBlocks_map_intCast_mem_symplecticGroup ℝ h) hu
  have e (M : Matrix ι ι ℤ) : M.map ((↑) : ℤ → ℂ) = (M.map ((↑) : ℤ → ℝ)).map ofReal := by
    ext
    simp
  convert hτ.neg_inv.add_map_ofReal h2.neg using 1
  rw [e c, e d, inv_map_ofReal hu.ne_zero, neg_add]
  ext i j
  simp [mul_apply]

theorem symplectic_action_eq {R : Type*} [CommRing R] {a b c d τ : Matrix ι ι R}
    (h : fromBlocks a b c d ∈ symplecticGroup ι R) (hd : IsUnit d.det) (hτ : IsUnit τ.det)
    (hN : IsUnit (τ⁻¹ + d⁻¹ * c).det) :
    c * τ + d = d * (τ⁻¹ + d⁻¹ * c) * τ ∧
    (a * τ + b) * (c * τ + d)⁻¹ = d⁻¹ᵀ * (τ⁻¹ + d⁻¹ * c)⁻¹ * d⁻¹ + b * d⁻¹ := by
  obtain ⟨h1, -, h3⟩ := symplectic_fromBlocks_inv_relations h hd
  have e1 : c * τ + d = d * (τ⁻¹ + d⁻¹ * c) * τ := by
    rw [Matrix.mul_add, mul_nonsing_inv_cancel_left _ _ hd, Matrix.add_mul,
      nonsing_inv_mul_cancel_right _ _ hτ, add_comm]
  have hj : IsUnit (c * τ + d).det := by
    rw [e1, det_mul, det_mul]
    exact (hd.mul hN).mul hτ
  have e2 : a = d⁻¹ᵀ + b * d⁻¹ * c := by
    have := congrArg transpose h3
    rw [transpose_mul, h1.eq, transpose_transpose, transpose_sub, transpose_transpose] at this
    rw [this]
    abel
  have e3 : a * τ + b = d⁻¹ᵀ * τ + b * d⁻¹ * (c * τ + d) := by
    rw [Matrix.mul_add, nonsing_inv_mul_cancel_right _ _ hd, ← add_assoc, ← Matrix.mul_assoc,
      ← Matrix.add_mul, ← e2]
  refine ⟨e1, ?_⟩
  rw [e3, Matrix.add_mul, mul_nonsing_inv_cancel_right _ _ hj, e1, Matrix.mul_inv_rev,
    Matrix.mul_inv_rev, ← Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hτ, Matrix.mul_assoc]

theorem IsSiegel.riemannTheta_symplectic {τ : Matrix ι ι ℂ} (hτ : IsSiegel τ)
    (h : fromBlocks a b c d ∈ symplecticGroup ι ℤ) (hd : d.det ≠ 0)
    (hb : ∀ μ, Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ)) (hc : ∀ μ, Even (μ ⬝ᵥ (aᵀ * c) *ᵥ μ))
    {κ : Type*} [Fintype κ] (r : κ → ι → ℤ)
    (hr : Function.Bijective fun k =>
      (Submodule.Quotient.mk (r k) : (ι → ℤ) ⧸ LinearMap.range d.mulVecLin)) (z : ι → ℂ) :
    riemannTheta 0 0 ((a.map (↑) * τ + b.map (↑)) * (c.map (↑) * τ + d.map (↑))⁻¹)
        ((c.map (↑) * τ + d.map (↑))⁻¹ᵀ *ᵥ z) *
      cexp (-(π * I) * (z ⬝ᵥ ((c.map (↑) * τ + d.map (↑))⁻¹ * c.map (↑)) *ᵥ z)) =
    (∑ k, cexp (π * I * ((fun i => (r k i : ℂ)) ⬝ᵥ
        (b.map ((↑) : ℤ → ℂ) * (d.map ((↑) : ℤ → ℂ))⁻¹) *ᵥ fun i => (r k i : ℂ)))) *
      siegelGaussIntegral (τ⁻¹ + (d.map ((↑) : ℤ → ℂ))⁻¹ * c.map ((↑) : ℤ → ℂ))⁻¹ /
      siegelGaussIntegral τ * riemannTheta 0 0 τ z := by
  have hs := (symm_coprime_of_mem_symplecticGroup h).1
  have hu := isUnit_det_map_intCast ℂ hd
  have huR := isUnit_det_map_intCast ℝ hd
  have hN := hτ.neg_inv_add_inv_mul h hd
  have hG := sum_exp_pair_mul_exp h hd hb hc r hr
  have hφ := ratCircleChar_pairQuadraticForm_mk hd hs hb
  have eR (M : Matrix ι ι ℤ) : M.map ((↑) : ℤ → ℂ) = (M.map ((↑) : ℤ → ℝ)).map ofReal := by
    ext
    simp
  have eD : (d.map ((↑) : ℤ → ℂ))⁻¹ = (d.map ((↑) : ℤ → ℝ))⁻¹.map ofReal := by
    rw [eR d, inv_map_ofReal huR.ne_zero]
  have hBR := (symplectic_fromBlocks_inv_relations
    (fromBlocks_map_intCast_mem_symplecticGroup ℝ h) huR).1
  have eB : b.map ((↑) : ℤ → ℂ) * (d.map ((↑) : ℤ → ℂ))⁻¹ =
      (b.map ((↑) : ℤ → ℝ) * (d.map ((↑) : ℤ → ℝ))⁻¹).map ofReal := by
    rw [eD]
    ext i j
    simp [mul_apply]
  have hcast := intCast_mulVec_complex d
  have hC := fromBlocks_map_intCast_mem_symplecticGroup ℂ h
  set A := a.map ((↑) : ℤ → ℂ)
  set B := b.map ((↑) : ℤ → ℂ)
  set C := c.map ((↑) : ℤ → ℂ)
  set D := d.map ((↑) : ℤ → ℂ)
  set N := τ⁻¹ + D⁻¹ * C with hNdef
  have hNu : IsUnit N.det := by
    have := hN.isUnit_det
    rw [det_neg] at this
    exact isUnit_of_mul_isUnit_right this
  have hNs : N.IsSymm := by simpa using hN.isSymm.neg
  have hσ : IsSiegel N⁻¹ := by
    have e : (-N)⁻¹ = -N⁻¹ := inv_eq_right_inv (by rw [neg_mul_neg, mul_nonsing_inv _ hNu])
    simpa [e] using hN.neg_inv
  have hτs : τ⁻¹.IsSymm := by simpa using hτ.neg_inv.isSymm.neg
  obtain ⟨e1, e2⟩ := symplectic_action_eq hC hu hτ.isUnit_det hNu
  rw [← hNdef] at e1 e2
  have e3 : (C * τ + D)⁻¹ = τ⁻¹ * N⁻¹ * D⁻¹ := by
    rw [e1, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]
  have hγ : IsSiegel (D⁻¹ᵀ * N⁻¹ * D⁻¹ + B * D⁻¹) := by
    rw [eB, eD]
    exact (hσ.transpose_mul_mul (isUnit_nonsing_inv_det _ huR).ne_zero).add_map_ofReal hBR
  have e4 : (C * τ + D)⁻¹ᵀ *ᵥ z = D⁻¹ᵀ *ᵥ N⁻¹ *ᵥ τ⁻¹ *ᵥ z := by
    rw [e3, transpose_mul, transpose_mul, hσ.isSymm.eq, hτs.eq, mulVec_mulVec, mulVec_mulVec,
      Matrix.mul_assoc]
  have e5 : z ⬝ᵥ ((C * τ + D)⁻¹ * C) *ᵥ z =
      z ⬝ᵥ τ⁻¹ *ᵥ z - (N⁻¹ *ᵥ τ⁻¹ *ᵥ z) ⬝ᵥ τ⁻¹ *ᵥ z := by
    rw [e3, Matrix.mul_assoc, show D⁻¹ * C = N - τ⁻¹ by rw [hNdef]; abel, Matrix.mul_sub,
      nonsing_inv_mul_cancel_right _ _ hNu, sub_mulVec, dotProduct_sub, ← mulVec_mulVec,
      ← mulVec_mulVec, dotProduct_mulVec_comm_of_isSymm hτs z (N⁻¹ *ᵥ _)]
  set x : κ → ι → ℝ := fun k => (d.map ((↑) : ℤ → ℝ))⁻¹ *ᵥ fun i => (r k i : ℝ) with hx
  have hx' (k : κ) : (fun i => (x k i : ℂ)) = D⁻¹ *ᵥ fun i => (r k i : ℂ) := by
    rw [eD]
    exact ofReal_mulVec_eq _ _

  have t1 (k : κ) (m : ι → ℤ) :
      riemannThetaTerm 0 0 (D⁻¹ᵀ * N⁻¹ * D⁻¹ + B * D⁻¹) (D⁻¹ᵀ *ᵥ N⁻¹ *ᵥ τ⁻¹ *ᵥ z) (r k + d *ᵥ m) =
        cexp (π * I * ((fun i => (r k i : ℂ)) ⬝ᵥ (B * D⁻¹) *ᵥ fun i => (r k i : ℂ))) *
          riemannThetaTerm (x k) 0 N⁻¹ (N⁻¹ *ᵥ τ⁻¹ *ᵥ z) m := by
    have q1 : (Submodule.Quotient.mk (r k) : (ι → ℤ) ⧸ LinearMap.range d.mulVecLin) =
        Submodule.Quotient.mk (r k + d *ᵥ m) :=
      (Submodule.Quotient.eq _).2 ⟨-m, by simp [mulVec_neg]⟩
    have q2 : (fun i => (m i : ℂ) + x k i) = D⁻¹ *ᵥ fun i => ((r k + d *ᵥ m) i : ℂ) := by
      have : (fun i => ((r k + d *ᵥ m) i : ℂ)) =
          (fun i => (r k i : ℂ)) + fun i => ((d *ᵥ m) i : ℂ) := by
        ext
        simp
      rw [this, hcast, mulVec_add, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec, ← hx',
        add_comm]
      rfl
    rw [← hφ, q1, hφ, riemannThetaTerm_zero_zero, riemannThetaTerm, q2, ← Complex.exp_add]
    generalize (fun i => ((r k + d *ᵥ m) i : ℂ)) = n
    congr 1
    simp only [Pi.zero_apply, ofReal_zero, add_zero]
    rw [add_mulVec, dotProduct_add, ← mulVec_mulVec n (D⁻¹ᵀ * N⁻¹), ← mulVec_mulVec _ D⁻¹ᵀ,
      dotProduct_mulVec n D⁻¹ᵀ, dotProduct_mulVec n D⁻¹ᵀ, vecMul_transpose]
    ring

  have t2 : ∑ k, cexp (π * I * ((fun i => (r k i : ℂ)) ⬝ᵥ (B * D⁻¹) *ᵥ fun i => (r k i : ℂ))) *
      riemannTheta 0 (x k) (-N) (τ⁻¹ *ᵥ z) =
      (∑ k, cexp (π * I * ((fun i => (r k i : ℂ)) ⬝ᵥ (B * D⁻¹) *ᵥ fun i => (r k i : ℂ)))) *
        riemannTheta 0 0 (-τ⁻¹) (τ⁻¹ *ᵥ z) := by
    refine (hasSum_sum fun k _ =>
      (hN.hasSum_riemannTheta 0 (x k) (τ⁻¹ *ᵥ z)).mul_left _).unique ?_
    convert (hτ.neg_inv.hasSum_riemannTheta 0 0 (τ⁻¹ *ᵥ z)).mul_left _ using 2 with m
    have q (k : κ) : riemannThetaTerm 0 (x k) (-N) (τ⁻¹ *ᵥ z) m =
        cexp (2 * π * I * ((fun i => (m i : ℂ)) ⬝ᵥ D⁻¹ *ᵥ fun i => (r k i : ℂ))) *
          riemannThetaTerm 0 0 (-N) (τ⁻¹ *ᵥ z) m := by
      have := riemannThetaTerm_add_ofReal 0 0 (x k) (-N) (τ⁻¹ *ᵥ z) m
      rw [zero_add] at this
      rw [← this, riemannThetaTerm_add, hx', mul_comm]
      simp
    simp only [q, ← mul_assoc _ _ (riemannThetaTerm ..), ← Finset.sum_mul]
    rw [hG, mul_assoc, riemannThetaTerm_zero_zero, riemannThetaTerm_zero_zero, ← Complex.exp_add,
      hNdef, neg_mulVec, neg_mulVec, add_mulVec, dotProduct_neg, dotProduct_neg, dotProduct_add]
    congr 2
    ring
  rw [e2, e4, e5, riemannTheta,
    tsum_eq_sum_tsum_add_mulVec hd r hr (hγ.summable_riemannThetaTerm 0 0 _)]
  simp only [t1, tsum_mul_left]
  have t3 (k : κ) := hσ.riemannTheta_eq_neg_inv (x k) (N⁻¹ *ᵥ τ⁻¹ *ᵥ z)
  simp only [nonsing_inv_nonsing_inv _ hNu, mulVec_mulVec _ N N⁻¹, mul_nonsing_inv _ hNu,
    one_mulVec] at t3
  simp only [← riemannTheta_def, t3, mul_left_comm _ (siegelGaussIntegral N⁻¹ * _),
    ← Finset.mul_sum]
  rw [t2, hτ.riemannTheta_eq_neg_inv, mul_sub, Complex.exp_sub]
  field_simp [hτ.siegelGaussIntegral_ne_zero]

theorem IsSiegel.exists_riemannTheta_multiplier {τ : Matrix ι ι ℂ} (hτ : IsSiegel τ)
    (h : fromBlocks a b c d ∈ symplecticGroup ι ℤ) (hodd : Odd d.det)
    (hb : ∀ μ, Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ)) (hc : ∀ μ, Even (μ ⬝ᵥ (aᵀ * c) *ᵥ μ)) :
    ∃ l : ℂ, l ^ 2 = (ZMod.χ₄ (d.det : ZMod 4) : ℤ) *
      (c.map ((↑) : ℤ → ℂ) * τ + d.map ((↑) : ℤ → ℂ)).det ∧
      ∀ z : ι → ℂ, riemannTheta 0 0 ((a.map (↑) * τ + b.map (↑)) * (c.map (↑) * τ + d.map (↑))⁻¹)
          ((c.map (↑) * τ + d.map (↑))⁻¹ᵀ *ᵥ z) *
        cexp (-(π * I) * (z ⬝ᵥ ((c.map (↑) * τ + d.map (↑))⁻¹ * c.map (↑)) *ᵥ z)) =
        l * riemannTheta 0 0 τ z := by
  have hd : d.det ≠ 0 := by
    rintro h0
    simp [h0] at hodd
  obtain ⟨r, hr⟩ := exists_representatives_quotient_range_mulVecLin hd
  refine ⟨_, ?_, hτ.riemannTheta_symplectic h hd hb hc r hr⟩
  obtain ⟨hs, hco⟩ := symm_coprime_of_mem_symplecticGroup h
  have hN := hτ.neg_inv_add_inv_mul h hd
  have hNu : IsUnit (τ⁻¹ + (d.map ((↑) : ℤ → ℂ))⁻¹ * c.map ((↑) : ℤ → ℂ)).det := by
    have := hN.isUnit_det
    rw [det_neg] at this
    exact isUnit_of_mul_isUnit_right this
  have e1 := (symplectic_action_eq (fromBlocks_map_intCast_mem_symplecticGroup ℂ h)
    (isUnit_det_map_intCast ℂ hd) hτ.isUnit_det hNu).1
  rw [div_pow, mul_pow, sq_sum_exp_pair hodd hs hb hco r hr, e1, det_mul, det_mul, ← Int.cast_det]
  generalize τ⁻¹ + (d.map ((↑) : ℤ → ℂ))⁻¹ * c.map ((↑) : ℤ → ℂ) = N at hN hNu
  have hσ : IsSiegel N⁻¹ := by
    have e : (-N)⁻¹ = -N⁻¹ := inv_eq_right_inv (by rw [neg_mul_neg, mul_nonsing_inv _ hNu])
    simpa [e] using hN.neg_inv
  have h1 := hσ.siegelGaussIntegral_sq_mul_det
  have h2 := hτ.siegelGaussIntegral_sq_mul_det
  have h3 := det_nonsing_inv_mul_det _ hNu
  rw [det_smul] at h1 h2
  have h4 : (-I) ^ Fintype.card ι ≠ 0 := pow_ne_zero _ (by simp)
  rw [div_eq_iff (pow_ne_zero _ hτ.siegelGaussIntegral_ne_zero)]
  apply mul_left_cancel₀ h4
  linear_combination ((ZMod.χ₄ (d.det : ZMod 4) : ℤ) * (d.det : ℂ)) * (N.det * h1 - N.det * h2 -
    (-I) ^ Fintype.card ι * siegelGaussIntegral N⁻¹ ^ 2 * h3)

theorem odd_det_of_mem_symplecticGroup (h : fromBlocks a b c d ∈ symplecticGroup ι ℤ)
    (hb : ∀ i j, 2 ∣ b i j) : Odd d.det := by
  have h2 := (symplectic_fromBlocks_relations
    (fromBlocks_map_intCast_mem_symplecticGroup (ZMod 2) h)).2.1
  have hb0 : b.map ((↑) : ℤ → ZMod 2) = 0 := by
    ext i j
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).2 (hb i j)
  rw [hb0, Matrix.mul_zero, sub_zero] at h2
  have h3 := (isUnit_det_of_left_inverse h2).ne_zero
  rw [← Int.cast_det, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd] at h3
  rw [← Int.not_even_iff_odd, even_iff_two_dvd]
  exact h3

end General

open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

variable {g : ℕ} {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}

theorem differentiableOn_nonsing_inv_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n : Type} [Fintype n] [DecidableEq n] {M : E → Matrix n n ℂ} {U : Set E}
    (hM : ∀ i j, DifferentiableOn ℂ (fun x => M x i j) U) (hu : ∀ x ∈ U, IsUnit (M x).det)
    (i j : n) : DifferentiableOn ℂ (fun x => (M x)⁻¹ i j) U := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, adjugate_apply]
  refine ((ReciprocityTheory.MultiplicativeHeights.differentiableOn_det_of hM).inv fun x hx => (hu x hx).ne_zero).mul
    (ReciprocityTheory.MultiplicativeHeights.differentiableOn_det_of
      (F := fun k l x => (M x).updateRow j (Pi.single i 1) k l) fun k l => ?_)
  simp only [updateRow_apply]
  split_ifs
  · exact differentiableOn_const _
  · exact hM k l

theorem differentiableOn_matrix_mul_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n : Type*} [Fintype n] {M N : E → Matrix n n ℂ} {U : Set E}
    (hM : ∀ i j, DifferentiableOn ℂ (fun x => M x i j) U)
    (hN : ∀ i j, DifferentiableOn ℂ (fun x => N x i j) U) (i j : n) :
    DifferentiableOn ℂ (fun x => (M x * N x) i j) U :=
  DifferentiableOn.fun_sum fun k _ => (hM i k).mul (hN k j)

theorem differentiableOn_of_theta_transform (hγ : γ ∈ symplecticGroup (Fin g) ℤ)
    {l : Matrix (Fin g) (Fin g) ℂ → ℂ} (hl : ∀ τ ∈ SiegelH (Fin g), ∀ z,
      theta 0 0 (zAct γ τ z) (spAct γ τ) * eC (-expArg γ τ z / 2) = l τ * theta 0 0 z τ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {T : E → Matrix (Fin g) (Fin g) ℂ}
    {U : Set E} (hT : ∀ x ∈ U, T x ∈ SiegelH (Fin g))
    (h1 : ∀ i j, DifferentiableOn ℂ (fun x => T x i j) U) :
    DifferentiableOn ℂ (fun x => l (T x)) U := by
  intro x₀ hx₀
  have hS {τ : Matrix (Fin g) (Fin g) ℂ} (h : τ ∈ SiegelH (Fin g)) : IsSiegel τ := ⟨h.1, h.2⟩
  obtain ⟨z, hz⟩ := Function.ne_iff.1 ((hS (hT _ hx₀)).riemannTheta_ne_zero 0 0)
  have h0 (A B : Matrix (Fin g) (Fin g) ℂ) (i j : Fin g) :
      DifferentiableOn ℂ (fun x => (A * T x + B) i j) U :=
    (differentiableOn_matrix_mul_apply (M := fun _ => A) (fun _ _ => differentiableOn_const _)
      h1 i j).add_const _
  have h2 (i j : Fin g) : DifferentiableOn ℂ (fun x => (jAut γ (T x))⁻¹ i j) U :=
    differentiableOn_nonsing_inv_apply (M := fun x => jAut γ (T x)) (h0 _ _)
      (fun x hx => jAut_isUnit hγ (hT x hx)) i j
  have h3 : DifferentiableOn ℂ (fun x => riemannTheta 0 0 (T x) z) U :=
    differentiableOn_riemannTheta_comp 0 0 (fun x hx => hS (hT x hx)) h1 (differentiableOn_const _)
  have h4 : DifferentiableOn ℂ (fun x => riemannTheta 0 0 (spAct γ (T x)) (zAct γ (T x) z)) U :=
    differentiableOn_riemannTheta_comp 0 0 (fun x hx => hS (spAct_mem hγ (hT x hx)))
      (differentiableOn_matrix_mul_apply (N := fun x => (jAut γ (T x))⁻¹) (h0 _ _) h2)
      (differentiableOn_pi.2 fun i => DifferentiableOn.fun_sum (u := Finset.univ) fun k _ =>
        (h2 k i).mul_const (z k))
  have h5 : DifferentiableOn ℂ (fun x => expArg γ (T x) z) U :=
    DifferentiableOn.fun_sum (u := Finset.univ) fun i _ =>
      (DifferentiableOn.fun_sum (u := Finset.univ) fun k _ =>
      (differentiableOn_matrix_mul_apply (N := fun _ => (cMat γ).toBlocks₂₁) h2
        (fun _ _ => differentiableOn_const _) i k).mul_const (z k)).const_mul (z i)
  have h6 : DifferentiableOn ℂ (fun x => eC (-expArg γ (T x) z / 2)) U := by
    simp only [eC, div_eq_mul_inv]
    exact ((h5.neg.mul_const _).const_mul _).cexp
  have h7 := (h3 x₀ hx₀).continuousWithinAt.eventually_ne hz
  refine ((((h4 x₀ hx₀).mul (h6 x₀ hx₀)).mul ((h3 x₀ hx₀).inv hz)).congr_of_eventuallyEq ?_
    ((eq_mul_inv_iff_mul_eq₀ hz).2 (hl _ (hT _ hx₀) z).symm))
  filter_upwards [h7, self_mem_nhdsWithin] with x hx hx'
  exact (eq_mul_inv_iff_mul_eq₀ hx).2 (hl _ (hT _ hx') z).symm

theorem isHoloSiegel_of_theta_transform (hγ : γ ∈ symplecticGroup (Fin g) ℤ)
    {l : Matrix (Fin g) (Fin g) ℂ → ℂ} (hl : ∀ τ ∈ SiegelH (Fin g), ∀ z,
      theta 0 0 (zAct γ τ z) (spAct γ τ) * eC (-expArg γ τ z / 2) = l τ * theta 0 0 z τ) :
    IsHoloSiegel g l :=
  differentiableOn_of_theta_transform hγ hl (T := fun x : Fin g → Fin g → ℂ => phSym (of x))
    (fun _ hx => hx) fun i j => by
      simp only [phSym, Matrix.smul_apply, Matrix.add_apply, transpose_apply, of_apply]
      fun_prop

theorem exists_theta_multiplier_of_odd_det (hγ : γ ∈ symplecticGroup (Fin g) ℤ)
    (hodd : Odd γ.toBlocks₂₂.det)
    (hb : ∀ μ, Even (μ ⬝ᵥ (γ.toBlocks₂₂ᵀ * γ.toBlocks₁₂) *ᵥ μ))
    (hc : ∀ μ, Even (μ ⬝ᵥ (γ.toBlocks₁₁ᵀ * γ.toBlocks₂₁) *ᵥ μ)) :
    ∃ l : Matrix (Fin g) (Fin g) ℂ → ℂ, IsHoloSiegel g l ∧ ∀ τ ∈ SiegelH (Fin g),
      (∀ z, theta 0 0 (zAct γ τ z) (spAct γ τ) * eC (-expArg γ τ z / 2) = l τ * theta 0 0 z τ) ∧
      l τ ^ 2 = (ZMod.χ₄ (γ.toBlocks₂₂.det : ZMod 4) : ℤ) * (jAut γ τ).det := by
  have H (τ : Matrix (Fin g) (Fin g) ℂ) (hτ : τ ∈ SiegelH (Fin g)) : ∃ l : ℂ,
      (∀ z, theta 0 0 (zAct γ τ z) (spAct γ τ) * eC (-expArg γ τ z / 2) = l * theta 0 0 z τ) ∧
      l ^ 2 = (ZMod.χ₄ (γ.toBlocks₂₂.det : ZMod 4) : ℤ) * (jAut γ τ).det := by
    obtain ⟨l, h1, h2⟩ := IsSiegel.exists_riemannTheta_multiplier ⟨hτ.1, hτ.2⟩
      (by rwa [fromBlocks_toBlocks]) hodd hb hc
    refine ⟨l, fun z => ?_, h1⟩
    rw [eC, show 2 * π * I * (-expArg γ τ z / 2) = -(π * I) * expArg γ τ z by ring]
    exact h2 z
  choose! l hl using H
  exact ⟨l, isHoloSiegel_of_theta_transform hγ fun τ hτ => (hl τ hτ).1, hl⟩

theorem exists_theta_multiplier_of_two_dvd (hγ : γ ∈ symplecticGroup (Fin g) ℤ)
    (hb : ∀ i j, 2 ∣ γ.toBlocks₁₂ i j) (hc : ∀ i j, 2 ∣ γ.toBlocks₂₁ i j) :
    ∃ l : Matrix (Fin g) (Fin g) ℂ → ℂ, IsHoloSiegel g l ∧ ∀ τ ∈ SiegelH (Fin g),
      (∀ z, theta 0 0 (zAct γ τ z) (spAct γ τ) * eC (-expArg γ τ z / 2) = l τ * theta 0 0 z τ) ∧
      l τ ^ 2 = (ZMod.χ₄ (γ.toBlocks₂₂.det : ZMod 4) : ℤ) * (jAut γ τ).det :=
  exists_theta_multiplier_of_odd_det hγ
    (odd_det_of_mem_symplecticGroup (by rwa [fromBlocks_toBlocks]) hb)
    (even_dotProduct_mulVec_of_two_dvd hb _) (even_dotProduct_mulVec_of_two_dvd hc _)

theorem theta_char_transform (hγ : γ ∈ symplecticGroup (Fin g) ℤ) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ ∈ SiegelH (Fin g)) {l : ℂ}
    (hl : ∀ z, theta 0 0 (zAct γ τ z) (spAct γ τ) * eC (-expArg γ τ z / 2) = l * theta 0 0 z τ)
    {p q p' q' : Fin g → ℝ}
    (hp : p = γ.toBlocks₁₁ᵀ.map ((↑) : ℤ → ℝ) *ᵥ p' + γ.toBlocks₂₁ᵀ.map ((↑) : ℤ → ℝ) *ᵥ q')
    (hq : q = γ.toBlocks₁₂ᵀ.map ((↑) : ℤ → ℝ) *ᵥ p' + γ.toBlocks₂₂ᵀ.map ((↑) : ℤ → ℝ) *ᵥ q')
    (z : Fin g → ℂ) :
    theta p' q' (zAct γ τ z) (spAct γ τ) * eC (-expArg γ τ z / 2) =
      l * eC ((ofRealVec p' ⬝ᵥ ofRealVec q' - ofRealVec p ⬝ᵥ ofRealVec q) / 2) * theta p q z τ := by
  have hj := jAut_isUnit hγ hτ
  have hs := spAct_isSymm hγ hτ.1 hj
  have hP : ofRealVec p = (cMat γ).toBlocks₁₁ᵀ *ᵥ ofRealVec p' +
      (cMat γ).toBlocks₂₁ᵀ *ᵥ ofRealVec q' := by
    rw [hp, ofRealVec_add, ofRealVec_mulVec, ofRealVec_mulVec]
    rfl
  have hQ : ofRealVec q = (cMat γ).toBlocks₁₂ᵀ *ᵥ ofRealVec p' +
      (cMat γ).toBlocks₂₂ᵀ *ᵥ ofRealVec q' := by
    rw [hq, ofRealVec_add, ofRealVec_mulVec, ofRealVec_mulVec]
    rfl
  obtain ⟨-, -, -, r4, r5⟩ : _ ∧ _ ∧ _ ∧
      (cMat γ).toBlocks₂₁ * (cMat γ).toBlocks₂₂ᵀ = (cMat γ).toBlocks₂₂ * (cMat γ).toBlocks₂₁ᵀ ∧
      (cMat γ).toBlocks₂₂ * (cMat γ).toBlocks₁₁ᵀ - (cMat γ).toBlocks₂₁ * (cMat γ).toBlocks₁₂ᵀ = 1 :=
    symplectic_fromBlocks_relations (fromBlocks_map_intCast_mem_symplecticGroup ℂ
      (by rwa [fromBlocks_toBlocks] : fromBlocks γ.toBlocks₁₁ γ.toBlocks₁₂ γ.toBlocks₂₁
        γ.toBlocks₂₂ ∈ symplecticGroup (Fin g) ℤ))
  set u := τ *ᵥ ofRealVec p + ofRealVec q with hu
  have e1 : (jAut γ τ)⁻¹ᵀ *ᵥ u = spAct γ τ *ᵥ ofRealVec p' + ofRealVec q' := by
    have : u = (nAut γ τ)ᵀ *ᵥ ofRealVec p' + (jAut γ τ)ᵀ *ᵥ ofRealVec q' := by
      rw [hu, hP, hQ, nAut_eq, jAut_eq]
      simp only [transpose_add, transpose_mul, hτ.1.eq, add_mulVec, mulVec_add, mulVec_mulVec]
      abel
    rw [this, mulVec_add, mulVec_mulVec, mulVec_mulVec, ← transpose_mul, ← transpose_mul,
      mul_nonsing_inv _ hj, transpose_one, one_mulVec, ← spAct_eq, hs.eq]
  have e2 : ((jAut γ τ)⁻¹ * (cMat γ).toBlocks₂₁) *ᵥ u =
      ofRealVec p - (jAut γ τ)⁻¹ *ᵥ ofRealVec p' := by
    have : (cMat γ).toBlocks₂₁ *ᵥ u = jAut γ τ *ᵥ ofRealVec p - ofRealVec p' := by
      have h : (cMat γ).toBlocks₂₂ *ᵥ ofRealVec p - (cMat γ).toBlocks₂₁ *ᵥ ofRealVec q =
          ofRealVec p' := by
        rw [hP, hQ]
        simp only [mulVec_add, mulVec_mulVec]
        rw [r4, add_sub_add_right_eq_sub, ← sub_mulVec, r5, one_mulVec]
      rw [← h, hu, jAut_eq, mulVec_add, add_mulVec, mulVec_mulVec]
      abel
    rw [← mulVec_mulVec, this, mulVec_sub, mulVec_mulVec, nonsing_inv_mul _ hj, one_mulVec]
  have hK : ((jAut γ τ)⁻¹ * (cMat γ).toBlocks₂₁).IsSymm := by
    have : (cMat γ).toBlocks₂₁ * (jAut γ τ)ᵀ = jAut γ τ * (cMat γ).toBlocks₂₁ᵀ := by
      rw [jAut_eq, transpose_add, transpose_mul, hτ.1.eq, Matrix.mul_add, Matrix.add_mul, r4,
        Matrix.mul_assoc]
    rw [Matrix.IsSymm, transpose_mul, transpose_nonsing_inv,
      ← nonsing_inv_mul_cancel_left (jAut γ τ) (cMat γ).toBlocks₂₁ᵀ hj, ← this, Matrix.mul_assoc,
      mul_nonsing_inv_cancel_right _ _ (isUnit_det_transpose _ hj)]
  have e3 : zAct γ τ (z + u) = zAct γ τ z + spAct γ τ *ᵥ ofRealVec p' + ofRealVec q' := by
    rw [zAct, mulVec_add, e1, ← add_assoc, zAct]
  have e4 (v : Fin g → ℂ) : v ⬝ᵥ (jAut γ τ)⁻¹ *ᵥ ofRealVec p' =
      ofRealVec p' ⬝ᵥ (jAut γ τ)⁻¹ᵀ *ᵥ v := by
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
  have e5 : expArg γ τ (z + u) = expArg γ τ z +
      2 * (ofRealVec p ⬝ᵥ z - ofRealVec p' ⬝ᵥ zAct γ τ z) + (ofRealVec p ⬝ᵥ u -
        ofRealVec p' ⬝ᵥ (spAct γ τ *ᵥ ofRealVec p' + ofRealVec q')) := by
    rw [expArg, expArg, mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
      dot_mulVec_symm hK z u, e2, dotProduct_sub, dotProduct_sub, e4, e4, e1, zAct,
      dotProduct_comm z (ofRealVec p), dotProduct_comm u (ofRealVec p)]
    ring
  have h0 : ofRealVec (0 : Fin g → ℝ) = 0 := by
    ext
    simp [ofRealVec]
  have key := hl (z + u)
  have t1 := thetaCharShift_holds (Fin g) p' q' 0 0 (zAct γ τ z) (spAct γ τ) hs
  have t2 := thetaRealTransl_holds (Fin g) 0 0 p q z τ hτ.1
  rw [zero_add, zero_add, h0, add_zero] at t1 t2
  rw [e3, e5, hu, ← add_assoc z, t2] at key
  have aux {X Y Z V W A B : ℂ} (h : A * eC X = l * (eC Y * B)) (hV : V + Z + Y = W + X) :
      eC V * A * eC Z = l * eC W * B := by
    have hY : eC Y ≠ 0 := Complex.exp_ne_zero _
    have := congrArg eC hV
    rw [eC_add, eC_add, eC_add] at this
    apply mul_right_cancel₀ hY
    linear_combination A * this + eC W * h
  rw [t1]
  refine aux key ?_
  simp only [dotProduct_add]
  ring

theorem theta_halfVec_sq_transform (hγ : γ ∈ symplecticGroup (Fin g) ℤ)
    (hb : ∀ i j, 4 ∣ γ.toBlocks₁₂ i j) (hc : ∀ i j, 4 ∣ γ.toBlocks₂₁ i j) {k k' m m' : Fin g → ℤ}
    (hm : ∀ i, m i ≡ (γ.toBlocks₁₁ᵀ *ᵥ k) i [ZMOD 2])
    (hm' : ∀ i, m' i ≡ (γ.toBlocks₂₂ᵀ *ᵥ k') i [ZMOD 2])
    {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g)) (z : Fin g → ℂ) :
    theta (halfVec k) (halfVec k') (zAct γ τ z) (spAct γ τ) ^ 2 =
      (ZMod.χ₄ (γ.toBlocks₂₂.det : ZMod 4) : ℤ) * (jAut γ τ).det * eC (expArg γ τ z) *
        theta (halfVec m) (halfVec m') z τ ^ 2 := by
  have h24 : (2 : ℤ) ∣ 4 := by norm_num
  obtain ⟨l, -, hl⟩ := exists_theta_multiplier_of_two_dvd hγ (fun i j => h24.trans (hb i j))
    fun i j => h24.trans (hc i j)
  set n := γ.toBlocks₁₁ᵀ *ᵥ k + γ.toBlocks₂₁ᵀ *ᵥ k' with hn
  set n' := γ.toBlocks₁₂ᵀ *ᵥ k + γ.toBlocks₂₂ᵀ *ᵥ k' with hn'
  have hadd (x y : Fin g → ℤ) : halfVec (x + y) = halfVec x + halfVec y := by
    ext i
    simp [halfVec, add_div]
  have key := theta_char_transform hγ hτ (hl τ hτ).1 (p := halfVec n) (q := halfVec n')
    (p' := halfVec k) (q' := halfVec k') (by rw [mulVec_halfVec, mulVec_halfVec, hn, hadd])
    (by rw [mulVec_halfVec, mulVec_halfVec, hn', hadd]) z
  have hc' (i : Fin g) : 4 ∣ (γ.toBlocks₂₁ᵀ *ᵥ k') i :=
    Finset.dvd_sum (s := Finset.univ) fun j _ => (hc j i).mul_right (k' j)
  have hb' (i : Fin g) : 4 ∣ (γ.toBlocks₁₂ᵀ *ᵥ k) i :=
    Finset.dvd_sum (s := Finset.univ) fun j _ => (hb j i).mul_right (k j)
  have e1 : theta (halfVec n) (halfVec n') z τ ^ 2 = theta (halfVec m) (halfVec m') z τ ^ 2 := by
    rw [theta_sq_red n, theta_sq_red m]
    congr 3 with i
    · have h1 : m i % 2 = _ := hm i
      have h2 := hc' i
      rw [h1, hn, Pi.add_apply]
      omega
    · have h1 : m' i % 2 = _ := hm' i
      have h2 := hb' i
      rw [h1, hn', Pi.add_apply]
      omega
  obtain ⟨t, ht⟩ : 4 ∣ k ⬝ᵥ k' - n ⬝ᵥ n' := by
    have r5 := (symplectic_fromBlocks_relations
      (by rwa [fromBlocks_toBlocks] : fromBlocks γ.toBlocks₁₁ γ.toBlocks₁₂ γ.toBlocks₂₁
        γ.toBlocks₂₂ ∈ symplecticGroup (Fin g) ℤ)).2.2.2.2
    have e : k ⬝ᵥ k' = (γ.toBlocks₁₁ᵀ *ᵥ k) ⬝ᵥ (γ.toBlocks₂₂ᵀ *ᵥ k') -
        (γ.toBlocks₁₂ᵀ *ᵥ k) ⬝ᵥ (γ.toBlocks₂₁ᵀ *ᵥ k') := by
      rw [dotProduct_comm k, dotProduct_comm (_ *ᵥ k), dotProduct_comm (_ *ᵥ k),
        mulVec_transpose _ k', mulVec_transpose _ k', ← dotProduct_mulVec, ← dotProduct_mulVec,
        mulVec_mulVec, mulVec_mulVec, ← dotProduct_sub, ← sub_mulVec, r5, one_mulVec]
    have d1 (v : Fin g → ℤ) : 4 ∣ v ⬝ᵥ (γ.toBlocks₁₂ᵀ *ᵥ k) :=
      Finset.dvd_sum fun i _ => (hb' i).mul_left _
    have d2 (v : Fin g → ℤ) : 4 ∣ (γ.toBlocks₂₁ᵀ *ᵥ k') ⬝ᵥ v :=
      Finset.dvd_sum fun i _ => (hc' i).mul_right _
    have d3 := d1 (γ.toBlocks₁₁ᵀ *ᵥ k)
    have d4 := d2 n'
    have d5 := d2 (γ.toBlocks₁₂ᵀ *ᵥ k)
    rw [dotProduct_comm] at d5
    rw [e, hn, add_dotProduct]
    nth_rw 1 [hn']
    rw [dotProduct_add]
    omega
  have e2 : eC ((ofRealVec (halfVec k) ⬝ᵥ ofRealVec (halfVec k') -
      ofRealVec (halfVec n) ⬝ᵥ ofRealVec (halfVec n')) / 2) ^ 2 = 1 := by
    have ht' : ((k ⬝ᵥ k' : ℤ) : ℂ) - (n ⬝ᵥ n' : ℤ) = 4 * t := by exact_mod_cast ht
    rw [eC_pow, ← eC_int t]
    congr 1
    simp only [ofRealVec_halfVec, smul_dotProduct, dotProduct_smul, ofIntVec_dot, smul_eq_mul]
    push_cast
    linear_combination ht' / 4
  have e3 : eC (-expArg γ τ z / 2) ^ 2 * eC (expArg γ τ z) = 1 := by
    rw [eC_pow, ← eC_add, ← eC_zero]
    congr 1
    push_cast
    ring
  have key2 := congrArg (· ^ 2) key
  simp only [mul_pow, e1, e2, (hl τ hτ).2] at key2
  linear_combination eC (expArg γ τ z) * key2 -
    theta (halfVec k) (halfVec k') (zAct γ τ z) (spAct γ τ) ^ 2 * e3

theorem inversionStatement_holds : InversionStatement := by
  intro g a b τ hτ z
  have hS : IsSiegel τ := ⟨hτ.1, hτ.2⟩
  have h1 : theta b (-a) z τ = siegelGaussIntegral τ * cexp (-(π * I) * (z ⬝ᵥ (τ⁻¹ *ᵥ z)) -
      2 * π * I * (ofRealVec a ⬝ᵥ ofRealVec b)) * theta a b (τ⁻¹ *ᵥ z) (-τ⁻¹) :=
    hS.riemannTheta_char_eq_neg_inv a b z
  have h2 := hS.siegelGaussIntegral_sq_mul_det
  rw [det_smul, Fintype.card_fin] at h2
  have h3 : eC (z ⬝ᵥ (τ⁻¹ *ᵥ z)) * eC (2 * (ofRealVec a ⬝ᵥ ofRealVec b)) *
      cexp (-(π * I) * (z ⬝ᵥ (τ⁻¹ *ᵥ z)) - 2 * π * I * (ofRealVec a ⬝ᵥ ofRealVec b)) ^ 2 = 1 := by
    rw [eC, eC, sq, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    ring
  rw [h1]
  linear_combination (-theta a b (τ⁻¹ *ᵥ z) (-τ⁻¹) ^ 2) * h2 -
    theta a b (τ⁻¹ *ᵥ z) (-τ⁻¹) ^ 2 * (siegelGaussIntegral τ ^ 2 * ((-I) ^ g * τ.det)) * h3

theorem chiStatement_holds : ChiStatement := chi_of inversionStatement_holds spGen

end GlobalTheory
