import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IncMTranspose

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.kunf

theorem jw_sq_ks {R : Type} [CommRing R] (n : ℕ) (e : R) : jw n e * jw n e = e • 1 := by
  rw [jw, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]
  simp

private theorem map_jw_eq_self_of_involution {R : Type} [CommRing R] (s : R →+* R) (hs : ∀ x, s (s x) = x) {n : ℕ} (e : R)
    (hse : s e = e) : (jw n e).map s = jw n e := by
  unfold jw
  rw [Matrix.fromBlocks_map]
  congr 1
  · ext i j; simp
  · ext i j; simp [Matrix.one_apply]
  · ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, Matrix.smul_apply, h, hse]
  · ext i j; simp

theorem frame_inv_pf {R : Type} [CommRing R] (s : R →+* R) (hs : ∀ x, s (s x) = x) {n : ℕ} (e : R) (he : e * e = 1)
    (hse : s e = e) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) (hM : Mᵀ * jw n e * M.map s = jw n e) :
    M * Matrix.fromBlocks (M.toBlocks₂₂.map s)ᵀ (e • (M.toBlocks₁₂.map s)ᵀ) (e • (M.toBlocks₂₁.map s)ᵀ)
      (M.toBlocks₁₁.map s)ᵀ = 1 ∧
    Matrix.fromBlocks (M.toBlocks₂₂.map s)ᵀ (e • (M.toBlocks₁₂.map s)ᵀ) (e • (M.toBlocks₂₁.map s)ᵀ)
      (M.toBlocks₁₁.map s)ᵀ * M = 1 := by
  set N := Matrix.fromBlocks (M.toBlocks₂₂.map s)ᵀ (e • (M.toBlocks₁₂.map s)ᵀ) (e • (M.toBlocks₂₁.map s)ᵀ)
      (M.toBlocks₁₁.map s)ᵀ with hN
  have hss : (M.map s).map s = M := by ext i j; simp [hs]
  have hM' : (M.map s)ᵀ * jw n e * M = jw n e := by
    have := congrArg (fun X => X.map s) hM
    simp only [Matrix.map_mul, Matrix.transpose_map, map_jw_eq_self_of_involution s hs e hse, hss] at this
    simpa [Matrix.transpose_map] using this
  have hJ : jw n e * jw n e = e • 1 := jw_sq_ks n e
  have hK : N = e • (jw n e * (M.map s)ᵀ * jw n e) := by
    conv_rhs => rw [← Matrix.fromBlocks_toBlocks (M.map s)]
    simp only [jw, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul, hN]
    simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, smul_smul, he]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ext <;> simp
  have h1 : N * M = 1 := by
    rw [hK, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (M.map s)ᵀ, hM', hJ,
      smul_smul, he, one_smul]
  exact ⟨mul_eq_one_comm.mp h1, h1⟩

end PositivityTheory.SiegelWeilFormula.kunf

end
