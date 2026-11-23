import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich

open Matrix Polynomial UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

namespace UpperTheory.Reformulated.B.CubicCharpolyDiscriminant

private lemma charpoly_three {R : Type} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R) :
    M.charpoly = X ^ 3 - C M.trace * X ^ 2 + C M.adjugate.trace * X - C M.det := by
  simp [Matrix.charpoly, Matrix.det_fin_three, Matrix.trace_fin_three, Matrix.adjugate_fin_three,
    Matrix.charmatrix_apply_eq, Matrix.charmatrix_apply_ne]
  ring

private lemma charpoly_tw {R : Type} [CommRing R] [StarRing R] (A M : Matrix (Fin 3) (Fin 3) R)
    (hA : A * star A = 1) (hM : M * star M = 1) (h : M = A * A.map star) :
    star M.trace = M.trace ∧ M.charpoly = (X - 1) * (X ^ 2 - C (M.trace - 1) * X + 1) := by
  have h1 : star M.trace = M.trace := by
    subst h
    simp only [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three, Matrix.map_apply,
      star_add, star_mul', star_star]
    ring
  have h2 : M.det = 1 := by
    have e : A.map star = (star A)ᵀ := by
      ext i j
      simp [Matrix.star_apply]
    rw [h, det_mul, e, det_transpose, ← det_mul, hA, det_one]
  have h3 : M.adjugate = star M := by
    calc M.adjugate = M.adjugate * (M * star M) := by rw [hM, Matrix.mul_one]
      _ = star M := by rw [← Matrix.mul_assoc, adjugate_mul, h2, one_smul, Matrix.one_mul]
  refine ⟨h1, ?_⟩
  rw [charpoly_three, h3, h2, star_eq_conjTranspose, trace_conjTranspose, h1]
  simp only [map_sub, map_one]
  ring

open scoped Matrix.Norms.L2Operator in
private lemma disc_nonpos (M : Matrix (Fin 3) (Fin 3) ℂ) (hM : M ∈ unitary (Matrix (Fin 3) (Fin 3) ℂ)) (t : ℝ)
    (h : M.charpoly = (X - 1) * (X ^ 2 - C (t : ℂ) * X + 1)) : t ^ 2 - 4 ≤ 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s ^ 2 = t ^ 2 - 4 := ⟨√(t ^ 2 - 4), Real.sq_sqrt hc.le⟩
  set r : ℝ := (t + s) / 2 with hr
  have e : r ^ 2 - t * r + 1 = 0 := by rw [hr]; linarith
  have hroot : (r : ℂ) ∈ spectrum ℂ M := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, h]
    have e' : (r : ℂ) ^ 2 - t * r + 1 = 0 := by exact_mod_cast e
    simp [e']
  have hn := spectrum.norm_eq_one_of_unitary hM hroot
  rw [Complex.norm_real, Real.norm_eq_abs] at hn
  have h2 : r ^ 2 = 1 := by rw [← sq_abs, hn]; norm_num
  have h3 : t * r = 2 := by linarith
  have h4 : t ^ 2 = 4 := by
    calc t ^ 2 = (t * r) ^ 2 := by rw [mul_pow, h2, mul_one]
      _ = 4 := by rw [h3]; norm_num
  linarith

private lemma exists_emb {F : Type} [Field F] (Δ : F) (σ : F →+* ℝ) (h : σ Δ < 0) :
    ∃ φ : Lsq F Δ →+* ℂ, (∀ x, φ (star x) = star (φ x)) ∧ ∀ a, φ (algebraMap F _ a) = σ a := by
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s * s = -σ Δ := ⟨√(-σ Δ), Real.mul_self_sqrt (by linarith)⟩
  refine ⟨{ toFun := fun x => ⟨σ x.re, σ x.im * s⟩
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, ?_, ?_⟩
  · apply Complex.ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · intro x y
    apply Complex.ext
    · simp
      linear_combination (σ x.im * σ y.im) * hs
    · simp
      ring
  · apply Complex.ext <;> simp
  · intro x y
    apply Complex.ext
    · simp
    · simp
      ring
  · intro x
    apply Complex.ext <;> simp
  · intro a
    apply Complex.ext <;> simp

end UpperTheory.Reformulated.B.CubicCharpolyDiscriminant

theorem UpperTheory.Reformulated.B.CubicCharpolyDiscriminant.tauEx :
    UpperTheory.V.Z.Sym.Glob.TauEx := by
  intro F _ _ Δ D hD δ
  set M : U3 Δ := δ * theta Δ δ with hMdef
  obtain ⟨h1, h2⟩ := charpoly_tw (δ : Matrix (Fin 3) (Fin 3) (Lsq F Δ)) (M : Matrix (Fin 3) (Fin 3) (Lsq F Δ))
    δ.2.2 M.2.2 rfl
  have him : (M : Matrix (Fin 3) (Fin 3) (Lsq F Δ)).trace.im = 0 := by
    have := congrArg QuadraticAlgebra.im h1
    rw [QuadraticAlgebra.im_star] at this
    linear_combination (-1 / 2 : F) * this
  have hτ : algebraMap F (Lsq F Δ) ((M : Matrix (Fin 3) (Fin 3) (Lsq F Δ)).trace.re - 1) =
      (M : Matrix (Fin 3) (Fin 3) (Lsq F Δ)).trace - 1 := by
    ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, him]
  rw [← hτ] at h2
  generalize (M : Matrix (Fin 3) (Fin 3) (Lsq F Δ)).trace.re - 1 = τ at h2
  refine ⟨τ, h2, fun hne σ => ?_⟩
  obtain ⟨φ, hφ, hφa⟩ := exists_emb Δ σ (hD.neg σ)
  have hs : star ((M : Matrix (Fin 3) (Fin 3) (Lsq F Δ)).map φ) = (star (M : Matrix (Fin 3) (Fin 3) (Lsq F Δ))).map φ := by
    ext i j
    simp only [Matrix.star_apply, Matrix.map_apply, hφ]
  have hu : (M : Matrix (Fin 3) (Fin 3) (Lsq F Δ)).map φ ∈ unitary (Matrix (Fin 3) (Fin 3) ℂ) := by
    constructor
    · rw [hs, ← Matrix.map_mul, M.2.1, Matrix.map_one _ (map_zero φ) (map_one φ)]
    · rw [hs, ← Matrix.map_mul, M.2.2, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hle := disc_nonpos _ hu (σ τ) (by
    rw [Matrix.charpoly_map, h2]
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_one, Polynomial.map_C, hφa])
  have hne' : σ (τ ^ 2 - 4) ≠ 0 := (map_ne_zero σ).2 hne
  have e : σ (τ ^ 2 - 4) = σ τ ^ 2 - 4 := by
    rw [map_sub, map_pow, map_ofNat]
  exact lt_of_le_of_ne (e ▸ hle) hne'
