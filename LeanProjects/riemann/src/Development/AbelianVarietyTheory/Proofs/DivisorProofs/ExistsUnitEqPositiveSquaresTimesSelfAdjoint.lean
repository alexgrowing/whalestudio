import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

open Matrix Polynomial

namespace GlobalTheory.Desc.SqLin

section Alg
variable {A : Type} [CommRing A] [Algebra ℚ A] [Module.Finite ℚ A]

theorem exists_casimir (τ : A →ₗ[ℚ] ℚ) (y : A) (hy : ∀ a, a ≠ 0 → 0 < τ (y * a ^ 2)) :
    ∃ (r : ℕ) (c : Fin r → ℚ) (e : Fin r → A), (∀ i, 0 < c i) ∧
      (∀ a, (∀ i, e i * a = 0) → a = 0) ∧
      ∀ a, τ (y * (∑ i, c i • e i ^ 2) * a) = LinearMap.trace ℚ A (LinearMap.mulLeft ℚ a) := by
  classical
  let β : LinearMap.BilinForm ℚ A := ((LinearMap.mul ℚ A).compr₂ (τ ∘ₗ LinearMap.mulLeft ℚ y))
  have hβ : ∀ a b, β a b = τ (y * (a * b)) := fun a b => rfl
  have hs : β.IsSymm := ⟨fun a b => by simp only [hβ, mul_comm a b, RingHom.id_apply]⟩
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (K := ℚ) (V := A) (B := β) ⟨hs.eq⟩
  have hpos : ∀ i, 0 < β (v i) (v i) := fun i => by
    rw [hβ, ← sq]; exact hy _ (v.ne_zero i)
  have hco : ∀ a i, β a (v i) = v.repr a i * β (v i) (v i) := by
    intro a i
    conv_lhs => rw [← v.sum_repr a]
    rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      have : β (v j) (v i) = 0 := hv hj
      simp [this]
    · simp
  refine ⟨_, fun i => (β (v i) (v i))⁻¹, v, fun i => inv_pos.2 (hpos i), ?_, ?_⟩
  · intro a ha
    have : (1 : A) * a = 0 := by
      rw [← v.sum_repr 1, Finset.sum_mul]
      simp [ha]
    simpa using this
  · intro a
    rw [LinearMap.trace_eq_matrix_trace ℚ v, Matrix.trace, Finset.mul_sum, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := hco (a * v i) i
    rw [hβ] at h1
    have h2 : y * (β (v i) (v i))⁻¹ • v i ^ 2 * a = (β (v i) (v i))⁻¹ • (y * (a * v i * v i)) := by
      rw [mul_smul_comm, smul_mul_assoc]; congr 1; ring
    rw [h2, map_smul, h1, smul_eq_mul, Matrix.diag_apply, LinearMap.toMatrix_apply]
    have := (hpos i).ne'
    simp only [LinearMap.mulLeft_apply]
    field_simp

theorem exists_inv (y : A) (hy : ∀ a, y * a = 0 → a = 0) : ∃ u, y * u = 1 := by
  have hinj : Function.Injective (LinearMap.mulLeft ℚ y) := by
    rw [injective_iff_map_eq_zero]; exact hy
  exact (LinearMap.injective_iff_surjective.1 hinj) 1

theorem exists_sum_sq (τ : A →ₗ[ℚ] ℚ) (h1 : ∀ a, a ≠ 0 → 0 < τ (a ^ 2)) (y : A)
    (hy : ∀ a, a ≠ 0 → 0 < τ (y * a ^ 2)) :
    ∃ (r : ℕ) (c : Fin r → ℚ) (e : Fin r → A), (∀ i, 0 < c i) ∧ y = ∑ i, c i • e i ^ 2 := by
  classical
  obtain ⟨r, c, e, hc, he, hK⟩ := exists_casimir τ y hy
  obtain ⟨s, d, f, hd, -, hL⟩ := exists_casimir τ 1 (by simpa using h1)
  have hnn : ∀ a, 0 ≤ τ (a ^ 2) := fun a => by
    by_cases h : a = 0
    · simp [h]
    · exact (h1 a h).le
  have hz : ∀ a, τ (a ^ 2) = 0 → a = 0 := fun a h => by
    by_contra h'
    exact (h1 a h').ne' h
  set K := ∑ i, c i • e i ^ 2 with hKd
  set L := ∑ i, d i • f i ^ 2 with hLd
  have hKL : y * K = L := by
    have := hK (y * K - L)
    rw [← hL, one_mul] at this
    refine sub_eq_zero.1 (hz _ ?_)
    rw [sq, sub_mul, map_sub, this, sub_self]
  obtain ⟨u, hu⟩ := exists_inv K (by
    intro a ha
    refine he a fun i => hz _ ?_
    have h0 : ∑ i, c i * τ ((e i * a) ^ 2) = 0 := by
      have : τ (K * a * a) = 0 := by rw [ha]; simp
      rw [← this, hKd, Finset.sum_mul, Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_mul_assoc, smul_mul_assoc, map_smul, smul_eq_mul]
      congr 2; ring
    rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (hc i).le (hnn _)] at h0
    exact (mul_eq_zero.1 (h0 i (Finset.mem_univ _))).resolve_left (hc i).ne')
  refine ⟨r * s, fun k => c (finProdFinEquiv.symm k).1 * d (finProdFinEquiv.symm k).2,
    fun k => e (finProdFinEquiv.symm k).1 * f (finProdFinEquiv.symm k).2 * u,
    fun k => mul_pos (hc _) (hd _), ?_⟩
  rw [Equiv.sum_comp finProdFinEquiv.symm
    (fun k : Fin r × Fin s => (c k.1 * d k.2) • (e k.1 * f k.2 * u) ^ 2), Fintype.sum_prod_type]
  have : y = K * L * u ^ 2 := by
    rw [← hKL]; linear_combination (-y * (K * u + 1)) * hu
  rw [this, hKd, hLd, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Algebra.smul_def, map_mul]
  ring

end Alg

open scoped MatrixOrder in

theorem exists_diag {n : ℕ} (T B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosDef)
    (hT : (B * T).PosDef) :
    ∃ (P Q : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ), P * Q = 1 ∧ Q * P = 1 ∧ (∀ i, 0 < d i) ∧
      T = P * diagonal d * Q := by
  obtain ⟨C, hC, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hB.isStrictlyPositive
  obtain ⟨C, rfl⟩ := hC
  have hH : (star (↑C⁻¹ : Matrix (Fin n) (Fin n) ℝ) * (star (C : Matrix (Fin n) (Fin n) ℝ) * C * T) *
      (↑C⁻¹ : Matrix (Fin n) (Fin n) ℝ)).PosDef :=
    (Matrix.IsUnit.posDef_star_left_conjugate_iff (Units.isUnit _)).2 hT
  have e : star (↑C⁻¹ : Matrix (Fin n) (Fin n) ℝ) * (star (C : Matrix (Fin n) (Fin n) ℝ) * C * T) *
      (↑C⁻¹ : Matrix (Fin n) (Fin n) ℝ) = C * T * (↑C⁻¹ : Matrix (Fin n) (Fin n) ℝ) := by
    rw [mul_assoc (star (C : Matrix (Fin n) (Fin n) ℝ)), ← mul_assoc (star _), ← star_mul,
      Units.mul_inv, star_one, one_mul]
  rw [e] at hH
  have hs := hH.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  set U := hH.1.eigenvectorUnitary
  have h1 : (U : Matrix (Fin n) (Fin n) ℝ) * star (U : Matrix (Fin n) (Fin n) ℝ) = 1 := U.2.2
  have h2 : star (U : Matrix (Fin n) (Fin n) ℝ) * (U : Matrix (Fin n) (Fin n) ℝ) = 1 := U.2.1
  refine ⟨(↑C⁻¹ : Matrix (Fin n) (Fin n) ℝ) * U, star (U : Matrix (Fin n) (Fin n) ℝ) * C,
    hH.1.eigenvalues, ?_, ?_, hH.eigenvalues_pos, ?_⟩
  · rw [mul_assoc, ← mul_assoc (U : Matrix (Fin n) (Fin n) ℝ), h1, one_mul, Units.inv_mul]
  · rw [mul_assoc, ← mul_assoc (C : Matrix (Fin n) (Fin n) ℝ), Units.mul_inv, one_mul, h2]
  · have : T = (↑C⁻¹ : Matrix (Fin n) (Fin n) ℝ) * (C * T * (↑C⁻¹ : Matrix (Fin n) (Fin n) ℝ)) * C := by
      simp [mul_assoc]
    refine this.trans ?_
    conv_lhs => rw [hs]
    simp [mul_assoc]

theorem aeval_map_eq {n : ℕ} (T : Matrix (Fin n) (Fin n) ℚ) (P Q : Matrix (Fin n) (Fin n) ℝ)
    (d : Fin n → ℝ) (h1 : P * Q = 1) (h2 : Q * P = 1)
    (hT : T.map (Rat.cast : ℚ → ℝ) = P * diagonal d * Q) (p : ℚ[X]) :
    (aeval T p).map (Rat.cast : ℚ → ℝ) = P * diagonal (fun k => aeval (d k) p) * Q := by
  have hm : ∀ M : Matrix (Fin n) (Fin n) ℚ,
      M.map (Rat.cast : ℚ → ℝ) = (Rat.castHom ℝ).mapMatrix M := fun M => rfl
  induction p using Polynomial.induction_on with
  | C a =>
    have : (diagonal fun _ : Fin n => (a : ℝ)) = (a : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
      ext i j; by_cases h : i = j <;> simp [h, one_apply]
    simp only [aeval_C, eq_ratCast, this, Matrix.mul_smul, Matrix.smul_mul, mul_one, h1]
    ext i j; by_cases h : i = j <;> simp [h, one_apply, Matrix.algebraMap_matrix_apply]
  | add p q hp hq =>
    simp only [map_add]
    rw [hm, map_add, ← hm, ← hm, hp, hq, ← diagonal_add, mul_add, add_mul]
  | monomial m a h =>
    rw [pow_succ, ← mul_assoc, map_mul, hm, map_mul, ← hm, ← hm, h, aeval_X, hT]
    have : ∀ D E : Matrix (Fin n) (Fin n) ℝ, P * D * Q * (P * E * Q) = P * (D * E) * Q := by
      intro D E
      calc P * D * Q * (P * E * Q) = P * D * (Q * P) * E * Q := by simp only [mul_assoc]
        _ = _ := by rw [h2]; simp only [mul_assoc, one_mul]
    rw [this, diagonal_mul_diagonal]
    simp [mul_assoc]

theorem main (n : ℕ) (Tm : Matrix (Fin n) (Fin n) ℚ) (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.PosDef) (hT : (B * Tm.map (Rat.cast : ℚ → ℝ)).PosDef) :
    ∃ (c₀ : ℚ) (r : ℕ) (c : Fin r → ℚ) (p : Fin r → Polynomial ℚ), 0 < c₀ ∧ (∀ i, 0 < c i) ∧
      (1 : Matrix (Fin n) (Fin n) ℚ) =
        c₀ • Tm + ∑ i, c i • ((Polynomial.aeval Tm (p i)) ^ 2 * Tm) := by
  classical
  obtain ⟨P, Q, d, h1, h2, hd, hD⟩ := exists_diag _ B hB hT
  have key := aeval_map_eq Tm P Q d h1 h2 hD
  let f : ℚ[X] →ₐ[ℚ] Matrix (Fin n) (Fin n) ℚ := aeval Tm
  let ι := Ideal.kerLiftAlg f
  have hι : Function.Injective ι := Ideal.kerLiftAlg_injective f
  have hιm : ∀ p, ι (Ideal.Quotient.mk _ p) = aeval Tm p := Ideal.kerLiftAlg_mk f
  haveI : Module.Finite ℚ (ℚ[X] ⧸ RingHom.ker f) := Module.Finite.of_injective ι.toLinearMap hι
  let τ : (ℚ[X] ⧸ RingHom.ker f) →ₗ[ℚ] ℚ := Matrix.traceLinearMap (Fin n) ℚ ℚ ∘ₗ ι.toLinearMap
  have hτ : ∀ p, ((τ (Ideal.Quotient.mk _ p) : ℚ) : ℝ) = ∑ k, aeval (d k) p := by
    intro p
    have : τ (Ideal.Quotient.mk _ p) = (aeval Tm p).trace := by rw [← hιm]; rfl
    have h3 : (((aeval Tm p).trace : ℚ) : ℝ) = ((aeval Tm p).map (Rat.cast : ℚ → ℝ)).trace := by
      simp [Matrix.trace]
    rw [this, h3, key, trace_mul_comm, ← mul_assoc, h2, one_mul, trace_diagonal]
  have hpos : ∀ q : ℚ[X], (∀ k, 0 < aeval (d k) q) → ∀ a : ℚ[X] ⧸ RingHom.ker f, a ≠ 0 →
      0 < τ (Ideal.Quotient.mk _ q * a ^ 2) := by
    intro q hq a ha
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [← map_pow, ← map_mul, ← Rat.cast_pos (K := ℝ), hτ]
    have : ∃ k, aeval (d k) p ≠ 0 := by
      by_contra h
      push Not at h
      apply ha
      apply hι
      rw [hιm, map_zero]
      have := key p
      simp only [h, diagonal_zero, mul_zero, zero_mul] at this
      ext i j
      simpa using congrFun (congrFun this i) j
    obtain ⟨k, hk⟩ := this
    refine Finset.sum_pos' (fun i _ => ?_) ⟨k, Finset.mem_univ _, ?_⟩
    · rw [map_mul, map_pow]; exact mul_nonneg (hq i).le (sq_nonneg _)
    · rw [map_mul, map_pow]; exact mul_pos (hq k) (by positivity)
  obtain ⟨N, hN⟩ := exists_rat_gt (∑ k, d k)
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (Finset.sum_nonneg fun i _ => (hd i).le) hN
  have hN0' : 0 < N := by exact_mod_cast hN0
  have hNk : ∀ k, d k < N := fun k =>
    lt_of_le_of_lt (Finset.single_le_sum (fun i _ => (hd i).le) (Finset.mem_univ k)) hN
  set x : ℚ[X] ⧸ RingHom.ker f := Ideal.Quotient.mk _ X with hx
  obtain ⟨u, hu⟩ := exists_inv x (by
    intro a ha
    by_contra h
    have := hpos X (by simpa using hd) a h
    rw [sq, ← mul_assoc, ← hx, ha] at this
    simp at this)
  obtain ⟨r, c, e, hc, he⟩ := exists_sum_sq τ (by simpa using hpos 1 (by simp)) _
    (hpos ((C N - X) * X) (fun k => by
      simpa using mul_pos (sub_pos.2 (hNk k)) (hd k)))
  choose p hp using fun i => Ideal.Quotient.mk_surjective (e i * u)
  refine ⟨N⁻¹, r, fun i => N⁻¹ * c i, p, inv_pos.2 hN0', fun i => mul_pos (inv_pos.2 hN0') (hc i), ?_⟩
  have hmain : (1 : ℚ[X] ⧸ RingHom.ker f) =
      N⁻¹ • x + ∑ i, (N⁻¹ * c i) • ((Ideal.Quotient.mk _ (p i)) ^ 2 * x) := by
    have e1 : ∑ i, (N⁻¹ * c i) • ((Ideal.Quotient.mk (RingHom.ker f) (p i)) ^ 2 * x) =
        N⁻¹ • ((∑ i, c i • e i ^ 2) * (u ^ 2 * x)) := by
      rw [Finset.sum_mul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hp, mul_smul, smul_mul_assoc, mul_pow, mul_assoc]
    have e2 : Ideal.Quotient.mk (RingHom.ker f) (C N) = algebraMap ℚ _ N := rfl
    rw [e1, ← he, map_mul, map_sub, e2, ← hx, ← smul_add]
    have e3 : x + (algebraMap ℚ _ N - x) * x * (u ^ 2 * x) = algebraMap ℚ _ N := by
      linear_combination ((algebraMap ℚ _ N - x) * (x * u + 1)) * hu
    rw [e3, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hN0'.ne', map_one]
  have := congrArg ι hmain
  simpa only [map_one, map_add, map_smul, map_sum, map_mul, map_pow, hx, hιm, aeval_X] using this

end GlobalTheory.Desc.SqLin
