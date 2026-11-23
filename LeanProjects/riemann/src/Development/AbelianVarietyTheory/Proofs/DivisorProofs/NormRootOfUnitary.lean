import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt

namespace GlobalTheory.UnitaryCharpolyRootNorm

open Matrix NumberField

theorem norm_root_of_unitary {m : Type} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) (hA : Aᴴ * A = 1) (z : ℂ)
    (hz : A.charpoly.IsRoot z) : ‖z‖ = 1 := by
  have hdet : (Matrix.scalar m z - A).det = 0 := by
    rw [← Matrix.eval_charpoly]; exact hz
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hAv : A *ᵥ v = z • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext i
    simp [Matrix.mulVec_diagonal]
  have h1 : star (A *ᵥ v) ⬝ᵥ (A *ᵥ v) = star v ⬝ᵥ v := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
  rw [hAv, star_smul, smul_dotProduct, dotProduct_smul, smul_smul] at h1
  have hne : star v ⬝ᵥ v ≠ 0 := by
    open scoped ComplexOrder in
    exact fun h => hv0 (dotProduct_star_self_eq_zero.mp h)
  have h2 : star z * z = 1 := by
    apply mul_right_cancel₀ hne
    rw [one_mul]; exact h1
  have h3 : ‖z‖ * ‖z‖ = 1 := by
    have := congrArg norm h2
    rwa [norm_mul, norm_star, norm_one] at this
  nlinarith [norm_nonneg z]

theorem norm_root_charpoly {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (γ : GlobalTheory.BCT.UE E n)
    (τ : E →+* ℂ) :
    ∀ z ∈ (Polynomial.map τ (Matrix.charpoly ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E))).roots,
      ‖z‖ = (1 : ℝ) := by
  intro z hz
  set g : Matrix (Fin n) (Fin n) E := ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) with hg
  have h : (Matrix.of fun i j => IsCMField.complexConj E (g j i)) * 1 * g = 1 := γ.2
  rw [mul_one] at h
  have hA : (g.map τ)ᴴ * g.map τ = 1 := by
    have e : (g.map τ)ᴴ = (Matrix.of fun i j => IsCMField.complexConj E (g j i)).map τ := by
      ext i j
      simp [IsCMField.complexEmbedding_complexConj]
    rw [e, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero τ) (map_one τ)]
  apply norm_root_of_unitary _ hA
  rw [Matrix.charpoly_map]
  exact Polynomial.isRoot_of_mem_roots hz

end GlobalTheory.UnitaryCharpolyRootNorm
