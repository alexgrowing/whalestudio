import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

private theorem re_dot_swap {n : ℕ} (y x : Fin n → ℂ) : (star y ⬝ᵥ x).re = (star x ⬝ᵥ y).re := by
  simp only [dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.star_apply, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

private theorem def_of_inv {n : ℕ} (M Mi : Matrix (Fin n) (Fin n) ℂ) (h1 : Mi * M = 1) (s : ℝ)
    (h : ∀ y : Fin n → ℂ, y ≠ 0 → 0 < s * (star y ⬝ᵥ (Mi *ᵥ y)).re) (x : Fin n → ℂ) (hx : x ≠ 0) :
    0 < s * (star x ⬝ᵥ (M *ᵥ x)).re := by
  have hy : M *ᵥ x ≠ 0 := by
    intro h0
    apply hx
    have := congrArg (fun v => Mi *ᵥ v) h0
    simpa [Matrix.mulVec_mulVec, h1] using this
  have := h _ hy
  rwa [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, re_dot_swap] at this

private theorem def_conj {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (s : ℝ)
    (h : ∀ y : Fin n → ℂ, y ≠ 0 → 0 < s * (star y ⬝ᵥ (M *ᵥ y)).re) (x : Fin n → ℂ) (hx : x ≠ 0) :
    0 < s * (star x ⬝ᵥ (M.map (starRingEnd ℂ) *ᵥ x)).re := by
  have hy : star x ≠ 0 := by
    intro h0
    apply hx
    simpa using congrArg star h0
  have key : star x ⬝ᵥ (M.map (starRingEnd ℂ) *ᵥ x) =
      starRingEnd ℂ (star (star x) ⬝ᵥ (M *ᵥ star x)) := by
    simp [dotProduct, Matrix.mulVec, map_sum, map_mul]
  rw [key, Complex.conj_re]
  exact h _ hy

private theorem inv_map_ring {n : ℕ} {R R' : Type*} [Field R] [Field R'] (f : R →+* R') (A : Matrix (Fin n) (Fin n) R)
    (hA : A.det ≠ 0) : (A⁻¹).map f = (A.map f)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA),
    Matrix.map_one _ (map_zero f) (map_one f)]

private theorem herm_N {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (H β : Matrix (Fin n) (Fin n) E)
    (hH : H.map (cj E) = H) (hT : Hᵀ = H) (hd : H.det ≠ 0) (hs : H⁻¹ * (β.map (cj E))ᵀ * H = β) (a b : Fin n) :
    IsCMField.complexConj E ((β * H⁻¹) a b) = (β * H⁻¹) b a := by
  have hHi : (H⁻¹).map (cj E) = H⁻¹ := by rw [inv_map_ring _ _ hd, hH]
  have hHiT : (H⁻¹)ᵀ = H⁻¹ := by rw [Matrix.transpose_nonsing_inv, hT]
  have key : ((β * H⁻¹).map (cj E))ᵀ = β * H⁻¹ := by
    rw [Matrix.map_mul, hHi, Matrix.transpose_mul, hHiT]
    conv_rhs => rw [← hs]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd), Matrix.mul_one]
  have := congrFun (congrFun key b) a
  rw [Matrix.transpose_apply, Matrix.map_apply] at this
  exact this

theorem UpperTheory.Gal.G1.pDefSign :
    DefSign := by
  classical
  intro E _ _ _ A n p _ S B
  have hT : (A.H n)ᵀ = A.H n := Matrix.diagonal_transpose _
  have hH' : (A.H n).map (cj E) = A.H n := by
    have h := congrArg Matrix.transpose (A.herm n)
    rw [Matrix.transpose_transpose] at h
    rw [h]
    exact hT
  have hsym : (A.H n)⁻¹ * ((mat S ↑B.β).map (cj E))ᵀ * A.H n = mat S ↑B.β := by
    have h := B.sym
    change MulOpposite.unop (hermStar (A.H n) (A.det_ne n) (mat S ↑B.β)) = mat S ↑B.β at h
    rw [hermStar_apply] at h
    change ((A.H n).map (cj E))⁻¹ * ((mat S ↑B.β).map (cj E))ᵀ * (A.H n).map (cj E) = _ at h
    rwa [hH'] at h
  refine ⟨herm_N _ _ hH' hT (A.det_ne n) hsym, ?_, ?_⟩
  · rw [Matrix.det_mul]
    refine mul_ne_zero ?_ ?_
    · have hu : IsUnit (mat S ↑B.β) := B.β.isUnit
      exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
    · rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
      exact inv_ne_zero (A.det_ne n)
  · intro τ x hx
    set v := InfinitePlace.mk τ with hvdef
    set ε : ℝ := if v = InfinitePlace.mk A.τ₀ then 1 else -1 with hεdef
    have hpos : ∀ y : Fin n → ℂ, y ≠ 0 → 0 < ε *
        (star y ⬝ᵥ ((((A.H n).map v.embedding)ᵀ * (mat S ↑(B.β⁻¹)).map v.embedding) *ᵥ y)).re := by
      intro y hy
      have hp := B.posR v y hy
      have hsig : sigPosH (S.G.gram_herm v) = sigPos (A.herm n) v.embedding := rfl
      rw [hsig] at hp
      have hme : InfinitePlace.mk v.embedding = v := InfinitePlace.mk_embedding v
      by_cases hv : v = InfinitePlace.mk A.τ₀
      · have h1 := ((S.sig v.embedding).1 (by rw [hme]; exact hv)).1
        rw [hεdef, if_pos hv, one_mul]
        exact hp.1 h1
      · have h0 := ((S.sig v.embedding).2 (by rw [hme]; exact hv)).1
        rw [hεdef, if_neg hv, neg_one_mul, neg_pos]
        exact hp.2 (by rw [h0]; exact zero_ne_one)
    have h1 : (((A.H n).map v.embedding)ᵀ * (mat S ↑(B.β⁻¹)).map v.embedding) *
        (mat S ↑B.β * (A.H n)⁻¹).map v.embedding = 1 := by
      have hb : mat S ↑(B.β⁻¹) * mat S ↑B.β = 1 := B.β.inv_mul
      have h2 : A.H n * mat S ↑(B.β⁻¹) * (mat S ↑B.β * (A.H n)⁻¹) = 1 := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (mat S ↑(B.β⁻¹)), hb, Matrix.one_mul,
          Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (A.det_ne n))]
      rw [← Matrix.transpose_map, hT, ← Matrix.map_mul, ← Matrix.map_mul, h2,
        Matrix.map_one _ (map_zero _) (map_one _)]
    have hM := def_of_inv _ _ h1 ε hpos
    rcases InfinitePlace.embedding_mk_eq τ with he | he
    · have he' : v.embedding = τ := he
      rw [he'] at hM
      exact hM x hx
    · have he' : v.embedding = ComplexEmbedding.conjugate τ := he
      rw [he'] at hM
      have hc := def_conj _ ε hM x hx
      have hcc : ((mat S ↑B.β * (A.H n)⁻¹).map (ComplexEmbedding.conjugate τ)).map (starRingEnd ℂ) =
          (mat S ↑B.β * (A.H n)⁻¹).map τ := by
        ext i j
        simp only [Matrix.map_apply, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
      rwa [hcc] at hc
