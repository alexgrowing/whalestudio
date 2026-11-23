import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.OppositeUnipotentWeylConj

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Alg

theorem gram_loc {m n : ℕ} (fr : Matrix (Fin m) (Fin m) ℂ) (J : Matrix (Fin m) (Fin m) ℂ) (ζ s : ℂ) (hζ : ζ ≠ 0)
    (hfr : ζ • (frᵀ * J * fr.map star) = s • 1) (u : Matrix (Fin m) (Fin n) ℂ) :
    (fr * u.map star)ᵀ * J * (fr * u.map star).map star = (ζ⁻¹ * s) • (uᴴ * u) := by
  have h1 : frᵀ * J * fr.map star = (ζ⁻¹ * s) • (1 : Matrix (Fin m) (Fin m) ℂ) := by
    rw [mul_smul, ← hfr, smul_smul, inv_mul_cancel₀ hζ, one_smul]
  have hmap : (fr * u.map star).map star = fr.map star * u := by
    ext i j
    simp [Matrix.mul_apply, star_sum]
  rw [hmap, Matrix.transpose_mul]
  calc (u.map star)ᵀ * frᵀ * J * (fr.map star * u)
        = (u.map star)ᵀ * (frᵀ * J * fr.map star) * u := by simp only [Matrix.mul_assoc]
    _ = (ζ⁻¹ * s) • (uᴴ * u) := by
        rw [h1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
        rfl

theorem trace_herm_real {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hA : Aᴴ = A) (hB : Bᴴ = B) :
    (((A * B).trace.re : ℝ) : ℂ) = (A * B).trace := by
  have h : star (A * B).trace = (A * B).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA, hB, Matrix.trace_mul_comm]
  have him : (A * B).trace.im = 0 := by
    have h' := congrArg Complex.im h
    rw [Complex.star_def, Complex.conj_im] at h'
    linarith
  exact Complex.ext (by simp) (by simp [him])

end Alg

end PositivityTheory.SiegelWeilFormula

end
