import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.CommuteOfUnitaryConjugate

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open Matrix

section Place

variable {m n : ℕ}

def T1 (A : Matrix (Fin m) (Fin m) ℂ) (C bw : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (x : Matrix (Fin m) (Fin n) ℂ)
    (V : Matrix (Fin m) (Fin n) ℂ) : ℂ :=
  trace ((x * (bw.toCols₂)ᵀ)ᵀ * A * (V * (bw.toCols₁)ᵀ).map star * Cᵀ)

def T2 (fi : Matrix (Fin m) (Fin m) ℂ) (x V : Matrix (Fin m) (Fin n) ℂ) : ℂ := trace ((fi * x)ᴴ * (fi * V))

def Sw (A fi : Matrix (Fin m) (Fin m) ℂ) (C bw biw : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (x : Matrix (Fin m) (Fin n) ℂ)
    (U : Matrix (Fin m) (Fin n ⊕ Fin n) ℂ) : ℂ :=
  (4 * Real.pi * Complex.I) * ((T1 A C bw x (U * biwᵀ).toCols₁).re : ℂ) -
    (4 * Real.pi) * ((T2 fi x (U * biwᵀ).toCols₂).re : ℂ)

theorem frame_block_pairing_sign {C bw : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ} {ε : ℤˣ} (hJ : bwᵀ * C * bw.map star = jE n ε) :
    (bw.toCols₂)ᵀ * C * (bw.toCols₁).map star = ((ε : ℤ) : ℂ) • 1 := by
  ext i j
  have h := congrFun (congrFun hJ (Sum.inr i)) (Sum.inl j)
  simp only [PositivityTheory.SiegelWeilFormula.KK.jE, Matrix.fromBlocks_apply₂₁] at h
  rw [← h]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.toCols₁_apply,
    Matrix.toCols₂_apply]

theorem mapStar_mul {a b c : Type} [Fintype b] (M : Matrix a b ℂ) (N : Matrix b c ℂ) :
    (M * N).map star = M.map star * N.map star := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, star_sum, star_mul']

theorem trace_form_sign_eq {A : Matrix (Fin m) (Fin m) ℂ} {C bw : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ} {ε : ℤˣ}
    (hJ : bwᵀ * C * bw.map star = jE n ε) (x V : Matrix (Fin m) (Fin n) ℂ) :
    T1 A C bw x V = ((ε : ℤ) : ℂ) * trace (xᵀ * A * V.map star) := by
  have h1 := PositivityTheory.SiegelWeilFormula.KK.frame_block_pairing_sign hJ
  have h2 : ((bw.toCols₁).map star)ᵀ * Cᵀ * bw.toCols₂ = ((ε : ℤ) : ℂ) • 1 := by
    have h := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_smul,
      Matrix.transpose_one, ← Matrix.mul_assoc] at h
    exact h
  unfold PositivityTheory.SiegelWeilFormula.KK.T1
  calc trace ((x * (bw.toCols₂)ᵀ)ᵀ * A * (V * (bw.toCols₁)ᵀ).map star * Cᵀ)
      = trace (bw.toCols₂ * (xᵀ * A * V.map star * (((bw.toCols₁).map star)ᵀ * Cᵀ))) := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, PositivityTheory.SiegelWeilFormula.KK.mapStar_mul,
          Matrix.transpose_map, Matrix.mul_assoc]
    _ = trace (xᵀ * A * V.map star * (((bw.toCols₁).map star)ᵀ * Cᵀ) * bw.toCols₂) :=
        Matrix.trace_mul_comm _ _
    _ = trace (xᵀ * A * V.map star * (((bw.toCols₁).map star)ᵀ * Cᵀ * bw.toCols₂)) := by
        simp only [Matrix.mul_assoc]
    _ = trace (xᵀ * A * V.map star * (((ε : ℤ) : ℂ) • 1)) := by rw [h2]
    _ = ((ε : ℤ) : ℂ) * trace (xᵀ * A * V.map star) := by
        rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]

theorem trace_transpose_star {a b : Type} [Fintype a] [Fintype b] (M N : Matrix a b ℂ) :
    trace (Mᵀ * N.map star) = star (trace (Mᴴ * N)) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.conjTranspose_apply, star_sum, star_mul', star_star]

theorem A_eq {A fr fi : Matrix (Fin m) (Fin m) ℂ} {sg : ℤˣ} {ζ : ℂ} (hfi' : fr * fi = 1) (hz : star ζ * ζ = 1)
    (hfr : ζ • (frᵀ * A * fr.map star) = ((sg : ℤ) : ℂ) • 1) :
    A = (((sg : ℤ) : ℂ) * star ζ) • (fiᵀ * fi.map star) := by
  have h1 : frᵀ * A * fr.map star = (((sg : ℤ) : ℂ) * star ζ) • (1 : Matrix (Fin m) (Fin m) ℂ) := by
    have h := congrArg (fun M => star ζ • M) hfr
    simp only [smul_smul, hz, one_smul] at h
    rw [h, mul_comm]
  have hfi : fiᵀ * frᵀ = 1 := by rw [← Matrix.transpose_mul, hfi', Matrix.transpose_one]
  have hfi2 : fr.map star * fi.map star = 1 := by
    rw [← PositivityTheory.SiegelWeilFormula.KK.mapStar_mul, hfi']
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  calc A = fiᵀ * frᵀ * A * (fr.map star * fi.map star) := by
        rw [hfi, hfi2, Matrix.one_mul, Matrix.mul_one]
    _ = fiᵀ * (frᵀ * A * fr.map star) * fi.map star := by simp only [Matrix.mul_assoc]
    _ = fiᵀ * ((((sg : ℤ) : ℂ) * star ζ) • (1 : Matrix (Fin m) (Fin m) ℂ)) * fi.map star := by rw [h1]
    _ = (((sg : ℤ) : ℂ) * star ζ) • (fiᵀ * fi.map star) := by
        rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

theorem trace_form_dual_eq {A fr fi : Matrix (Fin m) (Fin m) ℂ} {C bw : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ} {ε sg : ℤˣ} {ζ : ℂ} (hfi' : fr * fi = 1) (hz : star ζ * ζ = 1)
    (hfr : ζ • (frᵀ * A * fr.map star) = ((sg : ℤ) : ℂ) • 1) (hJ : bwᵀ * C * bw.map star = jE n ε)
    (x V : Matrix (Fin m) (Fin n) ℂ) :
    T1 A C bw x V = ((ε : ℤ) : ℂ) * ((((sg : ℤ) : ℂ) * star ζ) * star (T2 fi x V)) := by
  rw [PositivityTheory.SiegelWeilFormula.KK.trace_form_sign_eq hJ,
    PositivityTheory.SiegelWeilFormula.KK.A_eq hfi' hz hfr]
  congr 1
  unfold PositivityTheory.SiegelWeilFormula.KK.T2
  rw [← PositivityTheory.SiegelWeilFormula.KK.trace_transpose_star, Matrix.transpose_mul, PositivityTheory.SiegelWeilFormula.KK.mapStar_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  simp only [Matrix.mul_assoc]

theorem Sw_rel {A fr fi : Matrix (Fin m) (Fin m) ℂ} {C bw biw : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ} {ε sg : ℤˣ}
    {ζ : ℂ} (e2 : biw * bw = 1) (hfi' : fr * fi = 1) (hJ : bwᵀ * C * bw.map star = jE n ε)
    (hfr : ζ • (frᵀ * A * fr.map star) = ((sg : ℤ) : ℂ) • 1) (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I)
    (x : Matrix (Fin m) (Fin n) ℂ) (U U' : Matrix (Fin m) (Fin n ⊕ Fin n) ℂ)
    (hU : U' = (((((1 : ℤˣ) : ℤ) : ℂ) * Complex.I) • ((-(Complex.I * ((((ε : ℤ) : ℂ) * ((sg : ℤ) : ℂ)) * ζ))) •
      (1 : Matrix (Fin m) (Fin m) ℂ) * U * (bw * (jE n ε)ᵀ * biw)ᵀ))) :
    Sw A fi C bw biw x U' = Complex.I * Sw A fi C bw biw x U := by
  have hz : star ζ * ζ = 1 := by
    rcases hζ with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
  have hW : (bw * (PositivityTheory.SiegelWeilFormula.KK.jE n ε)ᵀ * biw)ᵀ * biwᵀ = biwᵀ * PositivityTheory.SiegelWeilFormula.KK.jE n ε := by
    rw [← Matrix.transpose_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e2, Matrix.one_mul,
      Matrix.transpose_mul, Matrix.transpose_transpose]
  have hUb : U' * biwᵀ = (((((1 : ℤˣ) : ℤ) : ℂ) * Complex.I) * (-(Complex.I * ((((ε : ℤ) : ℂ) * ((sg : ℤ) : ℂ)) * ζ)))) •
      (U * biwᵀ * PositivityTheory.SiegelWeilFormula.KK.jE n ε) := by
    rw [hU, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.smul_mul, smul_smul,
      Matrix.mul_assoc U _ biwᵀ, hW, ← Matrix.mul_assoc]
  have hYS1 : ∀ Y : Matrix (Fin m) (Fin n ⊕ Fin n) ℂ,
      (Y * PositivityTheory.SiegelWeilFormula.KK.jE n ε).toCols₁ = ((ε : ℤ) : ℂ) • Y.toCols₂ := by
    intro Y
    ext i j
    simp [PositivityTheory.SiegelWeilFormula.KK.jE, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
    try ring
  have hYS2 : ∀ Y : Matrix (Fin m) (Fin n ⊕ Fin n) ℂ,
      (Y * PositivityTheory.SiegelWeilFormula.KK.jE n ε).toCols₂ = Y.toCols₁ := by
    intro Y
    ext i j
    simp [PositivityTheory.SiegelWeilFormula.KK.jE, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
    try ring
  have hts1 : ∀ (c : ℂ) (M : Matrix (Fin m) (Fin n ⊕ Fin n) ℂ), (c • M).toCols₁ = c • M.toCols₁ :=
    fun _ _ => Matrix.ext fun _ _ => rfl
  have hts2 : ∀ (c : ℂ) (M : Matrix (Fin m) (Fin n ⊕ Fin n) ℂ), (c • M).toCols₂ = c • M.toCols₂ :=
    fun _ _ => Matrix.ext fun _ _ => rfl
  have hT : ∀ V, PositivityTheory.SiegelWeilFormula.KK.T1 A C bw x V =
      ((ε : ℤ) : ℂ) * ((((sg : ℤ) : ℂ) * star ζ) * star (PositivityTheory.SiegelWeilFormula.KK.T2 fi x V)) :=
    PositivityTheory.SiegelWeilFormula.KK.trace_form_dual_eq hfi' hz hfr hJ x
  have hN : ∀ (c : ℂ) (V : Matrix (Fin m) (Fin n) ℂ),
      PositivityTheory.SiegelWeilFormula.KK.T2 fi x (c • V) = c * PositivityTheory.SiegelWeilFormula.KK.T2 fi x V := by
    intro c V
    unfold PositivityTheory.SiegelWeilFormula.KK.T2
    rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  unfold PositivityTheory.SiegelWeilFormula.KK.Sw
  rw [hUb, hts1, hts2, hYS1, hYS2, smul_smul, hT, hT, hN, hN]
  rcases hζ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases Int.units_eq_one_or sg with rfl | rfl <;>
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

end Place

end PositivityTheory.SiegelWeilFormula.KK

end
