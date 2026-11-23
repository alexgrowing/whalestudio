import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.DoubledGroupTopologicalProperties

set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries.Grp

namespace PositivityTheory.SiegelWeilFormula.kfour

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

omit [NumberField F] [NumberField E] in
theorem int_units_sq (ε : ℤˣ) {R : Type} [CommRing R] : ((ε : ℤ) : R) * ((ε : ℤ) : R) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

variable (E) in

def w0 (n : ℕ) (ε : ℤˣ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E := Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0

omit [NumberField F] [NumberField E] in
theorem weyl_element_mul_self (ε : ℤˣ) : w0 E n ε * w0 E n ε = ((ε : ℤ) : E) • 1 := by
  simp only [w0, Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, zero_add,
    add_zero, Matrix.smul_mul, Matrix.one_mul]
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero]

omit [NumberField F] [NumberField E] in
theorem weyl_element_transpose_mul (ε : ℤˣ) : (w0 E n ε)ᵀ * w0 E n ε = 1 := by
  rw [w0, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, int_units_sq]

omit [NumberField E] in
theorem weyl_element_map_conj (ε : ℤˣ) : (w0 E n ε).map σ = w0 E n ε := by
  ext (i | i) (j | j) <;> simp [w0, Matrix.one_apply] <;> split_ifs <;> simp

omit [NumberField E] in
theorem mapσ_mul {α : Type} [Fintype α] (M N : Matrix α α E) : (M * N).map σ = M.map σ * N.map σ :=
  Matrix.map_mul (f := (σ : E →+* E))

variable (E) in

def w0GL (n : ℕ) (ε : ℤˣ) : GL (Fin n ⊕ Fin n) E where
  val := w0 E n ε
  inv := ((ε : ℤ) : E) • w0 E n ε
  val_inv := by rw [Matrix.mul_smul, weyl_element_mul_self, smul_smul, int_units_sq, one_smul]
  inv_val := by rw [Matrix.smul_mul, weyl_element_mul_self, smul_smul, int_units_sq, one_smul]

def wE (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ) : GL (Fin n ⊕ Fin n) E := b * w0GL E n ε * b⁻¹

theorem wE_unitary {b : GL (Fin n ⊕ Fin n) E} {ε : ℤˣ} (hε : b.1ᵀ * dbl Y.J * b.1.map σ = w0 E n ε) :
    (wE b ε).1ᵀ * dbl Y.J * (wE b ε).1.map σ = dbl Y.J := by
  have hb1 : (b⁻¹).1ᵀ * b.1ᵀ = 1 := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have hb2 : b.1.map σ * (b⁻¹).1.map σ = 1 := by
    rw [← mapσ_mul, Units.mul_inv, Matrix.map_one _ (map_zero σ) (map_one σ)]
  show (b.1 * w0 E n ε * (b⁻¹).1)ᵀ * dbl Y.J * (b.1 * w0 E n ε * (b⁻¹).1).map σ = dbl Y.J
  rw [mapσ_mul, mapσ_mul, weyl_element_map_conj, Matrix.transpose_mul, Matrix.transpose_mul]
  calc (b⁻¹).1ᵀ * ((w0 E n ε)ᵀ * b.1ᵀ) * dbl Y.J * (b.1.map σ * w0 E n ε * (b⁻¹).1.map σ)
      = (b⁻¹).1ᵀ * ((w0 E n ε)ᵀ * (b.1ᵀ * dbl Y.J * b.1.map σ) * w0 E n ε) * (b⁻¹).1.map σ := by
        simp only [Matrix.mul_assoc]
    _ = (b⁻¹).1ᵀ * (b.1ᵀ * dbl Y.J * b.1.map σ) * (b⁻¹).1.map σ := by
        rw [hε, weyl_element_transpose_mul, Matrix.one_mul]
    _ = ((b⁻¹).1ᵀ * b.1ᵀ) * dbl Y.J * (b.1.map σ * (b⁻¹).1.map σ) := by simp only [Matrix.mul_assoc]
    _ = dbl Y.J := by rw [hb1, hb2, Matrix.one_mul, Matrix.mul_one]

variable (σ Y) in

def wA (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ) (hε : b.1ᵀ * dbl Y.J * b.1.map σ = w0 E n ε) : G2 σ Y :=
  ⟨Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) (wE b ε), by
    have h := congrArg (fun M => M.map (inclR (F := F) (E := E) (AF F))) (wE_unitary hε)
    simp only [Matrix.map_mul, Matrix.transpose_map, incM_dbl, map_sigma_incM] at h
    exact h⟩

theorem wA_rat {b : GL (Fin n ⊕ Fin n) E} {ε : ℤˣ} (hε : b.1ᵀ * dbl Y.J * b.1.map σ = w0 E n ε) :
    wA σ Y b ε hε ∈ rat2 σ Y :=
  Subgroup.mem_subgroupOf.2 ⟨wE b ε, rfl⟩

theorem wA_inFrame {b : GL (Fin n ⊕ Fin n) E} {ε : ℤˣ} (hε : b.1ᵀ * dbl Y.J * b.1.map σ = w0 E n ε) :
    inFrame b (wA σ Y b ε hε) = Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0 := by
  unfold inFrame
  show incM F (b⁻¹).1 * incM F (b.1 * w0 E n ε * (b⁻¹).1) * incM F b.1 = _
  have e : (b⁻¹).1 * (b.1 * w0 E n ε * (b⁻¹).1) * b.1 = w0 E n ε := by
    simp only [Matrix.mul_assoc]
    rw [Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  simp only [incM]
  rw [← Matrix.map_mul, ← Matrix.map_mul, e]
  show incM F (w0 E n ε) = _
  rw [w0, incM_alt_alt, map_intCast]

theorem exists_w {b : GL (Fin n ⊕ Fin n) E} (hb : IsFrame2 σ Y b) :
    ∃ (ε : ℤˣ) (w : G2 σ Y), inFrame b w = Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0 ∧ w ∈ rat2 σ Y := by
  obtain ⟨ε, hε⟩ := hb.1
  exact ⟨ε, wA σ Y b ε hε, wA_inFrame hε, wA_rat hε⟩

theorem auxEx : AuxiliaryPrimeFunction := by
  intro F E _ _ _ _ _ σ d
  obtain ⟨ν, 𝓕, hν, h𝓕, h1⟩ := exists_cov (F := F) (E := E) d.m d.n
  obtain ⟨i1, i2, i3, i4⟩ := doubled_group_topological_properties σ d.Y
  exact ⟨⟨ν, hν, 𝓕, h𝓕, h1⟩, exists_w d.ok.frame, i1, i2, i3, i4⟩

end PositivityTheory.SiegelWeilFormula.kfour

end
