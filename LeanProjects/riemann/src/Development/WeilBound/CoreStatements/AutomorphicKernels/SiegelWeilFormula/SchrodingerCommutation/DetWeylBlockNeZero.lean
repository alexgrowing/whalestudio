import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SchrodingerCommutation.CommSchr

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.tweyl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

omit [NumberField F] [NumberField E] in
theorem int_units_sq (ε : ℤˣ) {R : Type} [CommRing R] : ((ε : ℤ) : R) * ((ε : ℤ) : R) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

omit [NumberField F] [NumberField E] in
theorem det_weyl_block_ne_zero {n : ℕ} (ε : ℤˣ) :
    (Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) E) (1 : Matrix (Fin n) (Fin n) E) (((ε : ℤ) : E) • (1 : Matrix (Fin n) (Fin n) E)) (0 : Matrix (Fin n) (Fin n) E)).det ≠ 0 := by
  set M := Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) E) (1 : Matrix (Fin n) (Fin n) E) (((ε : ℤ) : E) • (1 : Matrix (Fin n) (Fin n) E)) (0 : Matrix (Fin n) (Fin n) E)
  have hM : M * (((ε : ℤ) : E) • M) = 1 := by
    simp only [M, Matrix.mul_smul, Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul,
      Matrix.mul_one, zero_add, add_zero, Matrix.fromBlocks_smul, smul_zero, smul_smul, int_units_sq, one_smul,
      Matrix.smul_mul, Matrix.fromBlocks_one]
  intro h0
  have := congrArg Matrix.det hM
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

variable (d : SD σ)

theorem detY : d.Y.J.det ≠ 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  intro h0
  have hd : (dbl d.Y.J).det = 0 := by
    rw [dbl, Matrix.det_fromBlocks_zero₁₂, h0, zero_mul]
  have h := congrArg Matrix.det hε
  rw [Matrix.det_mul, Matrix.det_mul, hd, mul_zero, zero_mul] at h
  exact det_weyl_block_ne_zero ε h.symm

theorem signY : ∃ ε : ℤˣ, ∀ i j, σ (d.Y.J j i) = ((ε : ℤ) : E) * d.Y.J i j := by
  rcases d.ok.sign with ⟨-, h⟩ | ⟨-, h⟩
  · exact ⟨-1, fun i j => by rw [h]; simp⟩
  · exact ⟨1, fun i j => by rw [h]; simp⟩

omit [NumberField F] [NumberField E] in
theorem siegel_factor_ne {G H : Type} [Group G] [Group H] (χ : G →* Circle) (u : G) (m : H →* ℝ≥0) (v : H) (r : ℝ) :
    (χ u : ℂ) * (((m v : ℝ) ^ r : ℝ) : ℂ) ≠ 0 := by
  have hv : m v ≠ 0 := fun h => by
    have := map_mul m v v⁻¹
    rw [mul_inv_cancel, map_one, h, zero_mul] at this
    exact one_ne_zero this
  refine mul_ne_zero (Circle.coe_ne_zero _) (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos ?_ _).ne')
  exact lt_of_le_of_ne (NNReal.coe_nonneg _) (by exact_mod_cast hv.symm)

theorem exists_l_ne (hT : TBij) : ∃ φ ∈ schA F d.κ, d.l φ ≠ 0 := by
  obtain ⟨φz, hφz, hφz0⟩ := GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin F d.κ
  have hne : d.T φz ≠ 0 := fun h => hφz0 (by rw [(hT F E σ d).2.2 φz hφz h]; rfl)
  obtain ⟨X, hX⟩ : ∃ X, d.T φz X ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  exact ⟨_, GlobalTheory.HeisSchA.schr_mem_schA d.B.ψ (std d) _ φz hφz, hX⟩

end PositivityTheory.SiegelWeilFormula.tweyl
