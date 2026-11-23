import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

open GlobalTheory.WeilM
open scoped Matrix
open Matrix

namespace GlobalTheory.BigCell

variable {R : Type} [CommRing R] {β : Type} [Fintype β] [DecidableEq β]

theorem e1 : (fromCols (1 : Matrix β β R) (-1) : Matrix β (β ⊕ β) R) * (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R) = 0 := by
  simp [fromCols_mul_fromRows]

theorem e2 : (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R) * (fromCols (1 : Matrix β β R) 1 : Matrix β (β ⊕ β) R) +
    (fromRows (1 : Matrix β β R) (-1) : Matrix (β ⊕ β) β R) * (fromCols (1 : Matrix β β R) (-1) : Matrix β (β ⊕ β) R) =
    (2 : R) • (1 : Matrix (β ⊕ β) (β ⊕ β) R) := by
  rw [fromRows_mul_fromCols, fromRows_mul_fromCols, fromBlocks_add, ← fromBlocks_one, fromBlocks_smul]
  congr 1 <;> simp [two_smul]

theorem e3 (J : Matrix β β R) : (fromCols (1 : Matrix β β R) 1 : Matrix β (β ⊕ β) R) * dbl J =
    J * (fromCols (1 : Matrix β β R) (-1) : Matrix β (β ⊕ β) R) := by
  simp [dbl, fromCols_mul_fromBlocks, mul_fromCols]

theorem e4 (J : Matrix β β R) : dbl J * (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R) =
    (fromRows (1 : Matrix β β R) (-1) : Matrix (β ⊕ β) β R) * J := by
  simp [dbl, fromBlocks_mul_fromRows, fromRows_mul]

theorem e6 (J : Matrix β β R) : (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R) * J * (fromCols (1 : Matrix β β R) (-1) : Matrix β (β ⊕ β) R) +
    (fromRows (1 : Matrix β β R) (-1) : Matrix (β ⊕ β) β R) * J * (fromCols (1 : Matrix β β R) 1 : Matrix β (β ⊕ β) R) =
    (2 : R) • dbl J := by
  simp only [Matrix.mul_assoc, fromRows_mul, mul_fromCols, fromRows_fromCols_eq_fromBlocks, dbl, fromBlocks_smul]
  simp
  rw [fromBlocks_add]
  congr 1 <;> ext i j <;> simp <;> ring

theorem e7 (J : Matrix β β R) : (fromCols (1 : Matrix β β R) (-1) : Matrix β (β ⊕ β) R) * dbl J * (fromRows (1 : Matrix β β R) (-1) : Matrix (β ⊕ β) β R) = 0 := by
  simp [dbl, fromCols_mul_fromBlocks, fromCols_mul_fromRows]

theorem e5 (J : Matrix β β R) : (fromCols (1 : Matrix β β R) 1 : Matrix β (β ⊕ β) R) * dbl J * (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R) = 0 := by
  simp [dbl, fromCols_mul_fromBlocks, fromCols_mul_fromRows]

variable [Invertible (2 : R)]

theorem map_half (f : R →+* R) : f (⅟(2 : R)) = ⅟2 := by
  have e : f (⅟(2 : R)) * 2 = 1 := by
    have h := congrArg f (invOf_mul_self (2 : R))
    rwa [map_mul, map_ofNat, map_one] at h
  linear_combination (⅟(2 : R)) * e - f (⅟(2 : R)) * (invOf_mul_self (2 : R))

section Abstract

variable (f : R →+* R) (J : Matrix β β R) (K G : Matrix (β ⊕ β) (β ⊕ β) R) (Δ N : Matrix (β ⊕ β) β R)
  (Δt Nt : Matrix β (β ⊕ β) R) (D' : Matrix β β R)

theorem skew (hG : Gᵀ * K * G.map f = K) (hΔT : Δᵀ = Δt) (hNT : Nᵀ = Nt) (hΔtf : Δt.map f = Δt) (hNf : N.map f = N)
    (hNtf : Nt.map f = Nt) (e6 : Δ * J * Nt + N * J * Δt = (2 : R) • K) (e7 : Nt * K * N = 0)
    (hD : (Nt * G * N) * D' = 1) :
    (Δt * G * N * D')ᵀ * J + J * (Δt * G * N * D').map f = 0 := by
  have hΔtT : Δtᵀ = Δ := by rw [← hΔT, transpose_transpose]
  have hNtT : Ntᵀ = N := by rw [← hNT, transpose_transpose]
  have hDf : Nt * (G.map f * (N * D'.map f)) = 1 := by
    have := congrArg (Matrix.map · f) hD
    simp only [Matrix.map_mul, hNtf, hNf, Matrix.map_one f (map_zero f) (map_one f)] at this
    simpa only [Matrix.mul_assoc] using this
  have hDt : ∀ {γ : Type} (X : Matrix β γ R), D'ᵀ * (Nt * (Gᵀ * (N * X))) = X := by
    intro γ X
    have := congrArg transpose hD
    rw [transpose_mul, transpose_mul, transpose_mul, hNT, hNtT, transpose_one] at this
    calc D'ᵀ * (Nt * (Gᵀ * (N * X))) = (D'ᵀ * (Nt * (Gᵀ * N))) * X := by simp only [Matrix.mul_assoc]
      _ = X := by rw [this, Matrix.one_mul]
  have hxT : (Δt * G * N * D')ᵀ = D'ᵀ * (Nt * (Gᵀ * Δ)) := by
    simp only [transpose_mul, hNT, hΔtT, Matrix.mul_assoc]
  have hxf : (Δt * G * N * D').map f = Δt * (G.map f * (N * D'.map f)) := by
    simp only [Matrix.map_mul, hΔtf, hNf, Matrix.mul_assoc]
  have hY : Nt * (Gᵀ * ((Δ * J * Nt + N * J * Δt) * (G.map f * (N * D'.map f)))) = 0 := by
    rw [e6, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
      show Gᵀ * (K * (G.map f * (N * D'.map f))) = K * N * D'.map f by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hG, Matrix.mul_assoc],
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, e7, Matrix.zero_mul, smul_zero]
  calc (Δt * G * N * D')ᵀ * J + J * (Δt * G * N * D').map f
      = D'ᵀ * (Nt * (Gᵀ * ((Δ * J * Nt + N * J * Δt) * (G.map f * (N * D'.map f))))) := by
        rw [hxT, hxf]
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hDf, hDt, Matrix.mul_one]
    _ = 0 := by rw [hY, Matrix.mul_zero]

end Abstract

section Abstract2

variable (f : R →+* R) (J : Matrix β β R) (K G : Matrix (β ⊕ β) (β ⊕ β) R) (Δ N : Matrix (β ⊕ β) β R)
  (Δt Nt : Matrix β (β ⊕ β) R) (D' : Matrix β β R)

theorem mem_unitary (hG : Gᵀ * K * G.map f = K) (hΔT : Δᵀ = Δt) (hNT : Nᵀ = Nt) (hΔf : Δ.map f = Δ)
    (hΔtf : Δt.map f = Δt) (hNf : N.map f = N) (hNtf : Nt.map f = Nt)
    (e3 : Δt * K = J * Nt) (e4 : K * Δ = N * J) (e5 : Δt * K * Δ = 0)
    (e6 : Δ * J * Nt + N * J * Δt = (2 : R) • K) (e7 : Nt * K * N = 0) (hD : (Nt * G * N) * D' = 1) :
    (1 + ⅟(2 : R) • (Δ * (Δt * G * N * D') * Nt))ᵀ * K * (1 + ⅟(2 : R) • (Δ * (Δt * G * N * D') * Nt)).map f = K := by
  have hZ := skew f J K G Δ N Δt Nt D' hG hΔT hNT hΔtf hNf hNtf e6 e7 hD
  have hNtT : Ntᵀ = N := by rw [← hNT, transpose_transpose]
  set x := Δt * G * N * D' with hx
  have hMT : (Δ * x * Nt)ᵀ = N * (xᵀ * Δt) := by simp only [transpose_mul, hNtT, hΔT, Matrix.mul_assoc]
  have hMf : (Δ * x * Nt).map f = Δ * (x.map f * Nt) := by simp only [Matrix.map_mul, hΔf, hNtf, Matrix.mul_assoc]
  have hPT : (1 + ⅟(2 : R) • (Δ * x * Nt))ᵀ = 1 + ⅟(2 : R) • (N * (xᵀ * Δt)) := by
    rw [transpose_add, transpose_one, transpose_smul, hMT]
  have hPf : (1 + ⅟(2 : R) • (Δ * x * Nt)).map f = 1 + ⅟(2 : R) • (Δ * (x.map f * Nt)) := by
    rw [Matrix.map_add f (map_add f), Matrix.map_one f (map_zero f) (map_one f), Matrix.map_smul' _ _ _ (map_mul f),
      map_half, hMf]
  have A1 : N * (xᵀ * Δt) * K * (Δ * (x.map f * Nt)) = 0 := by
    simp only [Matrix.mul_assoc]
    rw [show Δt * (K * (Δ * (x.map f * Nt))) = 0 by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, e5, Matrix.zero_mul]]
    simp
  have A2 : N * (xᵀ * Δt) * K + K * (Δ * (x.map f * Nt)) = 0 := by
    calc _ = N * ((xᵀ * J + J * x.map f) * Nt) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, e3, ← Matrix.mul_assoc K Δ, e4]
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
      _ = 0 := by rw [hZ]; simp
  have expand : ∀ U V : Matrix (β ⊕ β) (β ⊕ β) R, (1 + ⅟(2 : R) • U) * K * (1 + ⅟(2 : R) • V) =
      K + ⅟(2 : R) • (U * K + K * V) + (⅟(2 : R) * ⅟(2 : R)) • (U * K * V) := by
    intro U V
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
      smul_add, smul_smul]
    abel
  rw [hPT, hPf, expand, A2, A1]
  simp

theorem mul_inv_eq (hNtΔ : Nt * Δ = 0) (x : Matrix β β R) :
    (1 + ⅟(2 : R) • (Δ * x * Nt)) * (1 - ⅟(2 : R) • (Δ * x * Nt)) = 1 ∧
    (1 - ⅟(2 : R) • (Δ * x * Nt)) * (1 + ⅟(2 : R) • (Δ * x * Nt)) = 1 := by
  have hM : (Δ * x * Nt) * (Δ * x * Nt) = 0 := by
    simp only [Matrix.mul_assoc]
    rw [show Nt * (Δ * (x * Nt)) = 0 by rw [← Matrix.mul_assoc, hNtΔ, Matrix.zero_mul]]
    simp
  constructor
  · simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hM, smul_zero]
    abel
  · simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hM, smul_zero]
    abel

theorem q_col (h2 : Δ * Δt + N * Nt = (2 : R) • 1) (hD' : D' * (Nt * G * N) = 1) :
    (1 - ⅟(2 : R) • (Δ * (Δt * G * N * D') * Nt)) * G * N = N * (⅟(2 : R) • (Nt * G * N)) := by
  have hNN : N * Nt = (2 : R) • 1 - Δ * Δt := by rw [← h2]; abel
  have hD'r : D' * (Nt * (G * N)) = 1 := by rw [← hD']; simp only [Matrix.mul_assoc]
  calc (1 - ⅟(2 : R) • (Δ * (Δt * G * N * D') * Nt)) * G * N = G * N - ⅟(2 : R) • (Δ * (Δt * (G * N))) := by
        simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_assoc, hD'r, Matrix.mul_one]
    _ = N * (⅟(2 : R) • (Nt * G * N)) := by
        rw [Matrix.mul_smul, show N * (Nt * G * N) = N * Nt * G * N by simp only [Matrix.mul_assoc], hNN]
        simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, smul_sub, smul_smul, invOf_mul_self, one_smul,
          Matrix.mul_assoc]

end Abstract2

theorem bigCell_factor : ∀ (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (c : R →ₐ[A] R) [Invertible (2 : R)]
    (β : Type) [Fintype β] [DecidableEq β] (J : Matrix β β R) (g : UG c (dbl J)),
    IsUnit (Matrix.fromCols (1 : Matrix β β R) (-1 : Matrix β β R) * ((g : GL (β ⊕ β) R) : Matrix (β ⊕ β) (β ⊕ β) R) *
      Matrix.fromRows (1 : Matrix β β R) (-1 : Matrix β β R)).det →
    ∃ (p q : UG c (dbl J)) (t s : GL β R),
      ((p : GL (β ⊕ β) R) : Matrix (β ⊕ β) (β ⊕ β) R) * Matrix.fromRows (1 : Matrix β β R) (1 : Matrix β β R) =
        Matrix.fromRows (1 : Matrix β β R) (1 : Matrix β β R) * (t : Matrix β β R) ∧
      ((q : GL (β ⊕ β) R) : Matrix (β ⊕ β) (β ⊕ β) R) * Matrix.fromRows (1 : Matrix β β R) (-1 : Matrix β β R) =
        Matrix.fromRows (1 : Matrix β β R) (-1 : Matrix β β R) * (s : Matrix β β R) ∧ g = p * q := by
  intro A R _ _ _ c _ β _ _ J g hdet
  set G : Matrix (β ⊕ β) (β ⊕ β) R := ((g : GL (β ⊕ β) R) : Matrix (β ⊕ β) (β ⊕ β) R) with hGdef
  set f : R →+* R := (c : R →+* R) with hf
  have hG : Gᵀ * dbl J * G.map f = dbl J := g.2
  have h1 : (1 : Matrix β β R).map f = 1 := Matrix.map_one f (map_zero f) (map_one f)
  have hm1 : (-1 : Matrix β β R).map f = -1 := by rw [Matrix.map_neg _ (map_neg f), h1]
  have hΔT : (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R)ᵀ = fromCols 1 1 := by
    rw [transpose_fromRows, transpose_one]
  have hNT : (fromRows (1 : Matrix β β R) (-1) : Matrix (β ⊕ β) β R)ᵀ = fromCols 1 (-1) := by
    rw [transpose_fromRows, transpose_one, transpose_neg, transpose_one]
  have hΔf : (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R).map f = fromRows 1 1 := by rw [fromRows_map, h1]
  have hNf : (fromRows (1 : Matrix β β R) (-1) : Matrix (β ⊕ β) β R).map f = fromRows 1 (-1) := by
    rw [fromRows_map, h1, hm1]
  have hΔtf : (fromCols (1 : Matrix β β R) 1 : Matrix β (β ⊕ β) R).map f = fromCols 1 1 := by rw [fromCols_map, h1]
  have hNtf : (fromCols (1 : Matrix β β R) (-1) : Matrix β (β ⊕ β) R).map f = fromCols 1 (-1) := by
    rw [fromCols_map, h1, hm1]
  set D : Matrix β β R := (fromCols (1 : Matrix β β R) (-1) : Matrix β (β ⊕ β) R) * G *
    (fromRows (1 : Matrix β β R) (-1) : Matrix (β ⊕ β) β R) with hDdef
  have hD : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hD' : D⁻¹ * D = 1 := Matrix.nonsing_inv_mul _ hdet
  set M : Matrix (β ⊕ β) (β ⊕ β) R := (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R) *
    ((fromCols (1 : Matrix β β R) 1 : Matrix β (β ⊕ β) R) * G * (fromRows (1 : Matrix β β R) (-1) : Matrix (β ⊕ β) β R) *
      D⁻¹) * (fromCols (1 : Matrix β β R) (-1) : Matrix β (β ⊕ β) R) with hMdef
  have hinv := mul_inv_eq (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R)
    (fromCols (1 : Matrix β β R) (-1) : Matrix β (β ⊕ β) R) e1
    ((fromCols (1 : Matrix β β R) 1 : Matrix β (β ⊕ β) R) * G * (fromRows (1 : Matrix β β R) (-1) : Matrix (β ⊕ β) β R) * D⁻¹)
  have hmem := mem_unitary f J (dbl J) G _ _ _ _ D⁻¹ hG hΔT hNT hΔf hΔtf hNf hNtf (e3 J) (e4 J) (e5 J) (e6 J) (e7 J) hD
  let P : GL (β ⊕ β) R := ⟨1 + ⅟(2 : R) • M, 1 - ⅟(2 : R) • M, hinv.1, hinv.2⟩
  let p : UG c (dbl J) := ⟨P, hmem⟩
  have hdetS : IsUnit (⅟(2 : R) • D).det := by
    rw [det_smul]
    exact ((isUnit_of_invertible (⅟(2 : R))).pow _).mul hdet
  let s : GL β R := ((Matrix.isUnit_iff_isUnit_det _).mpr hdetS).unit
  refine ⟨p, p⁻¹ * g, 1, s, ?_, ?_, (mul_inv_cancel_left p g).symm⟩
  · show (1 + ⅟(2 : R) • M) * (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R) = _
    rw [Units.val_one, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hMdef, Matrix.mul_assoc _ _
      (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R), e1, Matrix.mul_zero, smul_zero, add_zero]
  · show (1 - ⅟(2 : R) • M) * G * (fromRows (1 : Matrix β β R) (-1) : Matrix (β ⊕ β) β R) = _
    rw [IsUnit.unit_spec]
    exact q_col G _ _ _ _ D⁻¹ (e2) hD'

end GlobalTheory.BigCell
