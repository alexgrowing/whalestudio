import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaBijections.AlgInjective
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.TBij

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

section Gen

variable {R E' : Type} [CommRing R] [CommRing E'] [Algebra R E'] (c : E' →ₐ[R] E') {α β : Type} [Fintype α]
  [DecidableEq α] [Fintype β] [DecidableEq β]

theorem hTens_eq (JA : Matrix α α E') (JB : Matrix β β E') (x y : Matrix α β E') :
    hTens c JA JB x y = ∑ i, ∑ k, JA i k * (x * JB * (y.map c)ᵀ) i k := by
  simp only [hTens, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hTens_outer {ν : Type} [Fintype ν] (JA : Matrix α α E') (JB : Matrix β β E') (P P' : Matrix α ν E')
    (q q' : Matrix β ν E') (h : qᵀ * JB * q'.map c = 0) : hTens c JA JB (P * qᵀ) (P' * q'ᵀ) = 0 := by
  have e1 : (P' * q'ᵀ).map c = P'.map c * (q'.map c)ᵀ := by
    rw [show (P' * q'ᵀ).map c = P'.map c * (q'ᵀ).map c from Matrix.map_mul (f := c.toRingHom), Matrix.transpose_map]
  have e2 : P * qᵀ * JB * ((P' * q'ᵀ).map c)ᵀ = 0 := by
    rw [e1, Matrix.transpose_mul, Matrix.transpose_transpose]
    calc P * qᵀ * JB * (q'.map c * (P'.map c)ᵀ) = P * (qᵀ * JB * q'.map c) * (P'.map c)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h, Matrix.mul_zero, Matrix.zero_mul]
  rw [hTens_eq, e2]
  simp

end Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem incM_mul {α β γ : Type} [Fintype β] (x : Matrix α β E) (y : Matrix β γ E) :
    incM F (x * y) = incM F x * incM F y := Matrix.map_mul

theorem incM_transpose {α β : Type} (x : Matrix α β E) : incM F xᵀ = (incM F x)ᵀ := (Matrix.transpose_map).symm

theorem incM_one' {α : Type} [DecidableEq α] : incM F (1 : Matrix α α E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem incM_zero' {α β : Type} : incM F (0 : Matrix α β E) = 0 := Matrix.map_zero _ (map_zero _)

theorem cA_incM {α β : Type} (x : Matrix α β E) : (incM F x).map (cA σ) = incM F (x.map σ) := by
  ext i j
  show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ ((1 : AF F) ⊗ₜ[F] x i j) = (1 : AF F) ⊗ₜ[F] σ (x i j)
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem incM_dbl {β : Type} [DecidableEq β] (J : Matrix β β E) : incM F (dbl J) = dbl (incM F J) := by
  ext (i | i) (j | j) <;> simp [incM, dbl]

theorem incM_diagCols {β : Type} [DecidableEq β] : incM F (diagCols β : Matrix (β ⊕ β) β E) = diagCols β := by
  ext (i | i) j <;> simp [incM, diagCols, Matrix.one_apply] <;> split_ifs <;> simp

namespace Adp

variable (d : SD σ)

abbrev sy : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E) → Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E) → AF F :=
  symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J))

abbrev yy : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := incM F d.b.1.toCols₂

abbrev dg : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := diagCols (Fin d.n)

theorem sy_eq (w w' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : sy d w w' = om (d.dd.e w) (d.dd.e w') :=
  d.dd.form w w'

theorem sy_add_left (w₁ w₂ w' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    sy d (w₁ + w₂) w' = sy d w₁ w' + sy d w₂ w' := by
  simp only [sy_eq, map_add, om, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  ring

theorem sy_add_right (w w₁ w₂ : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    sy d w (w₁ + w₂) = sy d w w₁ + sy d w w₂ := by
  simp only [sy_eq, map_add, om, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  ring

theorem sy_smul_right (a : AF F) (w w' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    sy d w (a • w') = a * sy d w w' := by
  simp only [sy_eq, map_smul, om, Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

theorem sy_sum_left {ι : Type} (s : Finset ι) (a : ι → AF F) (v : ι → Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E))
    (w' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : sy d (∑ i ∈ s, a i • v i) w' = ∑ i ∈ s, a i * sy d (v i) w' := by
  simp only [sy_eq, map_sum, map_smul, om, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, sum_dotProduct,
    dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem sy_antisymm (w w' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : sy d w w' = -sy d w' w := by
  simp only [sy_eq, om]
  ring

theorem sy_diag (Z Z' : Matrix (Fin d.m) (Fin d.n) (AE F E)) : sy d (Z * (dg d)ᵀ) (Z' * (dg d)ᵀ) = 0 := by
  simp only [sy, symp]
  rw [hTens_outer _ _ _ _ _ _ _ (isLagr_diagCols (cA σ) (incM F d.Y.J)).1, mul_zero, map_zero]

theorem frame_iso : (d.b.1.toCols₂)ᵀ * dbl d.Y.J * d.b.1.toCols₂.map σ = 0 := by
  obtain ⟨ε, h⟩ := d.ok.frame.1
  have h2 := congrArg Matrix.toBlocks₂₂ h
  rw [Matrix.toBlocks_fromBlocks₂₂] at h2
  rw [← h2]
  ext i j
  simp [Matrix.toBlocks₂₂, Matrix.mul_apply, Matrix.toCols₂]

theorem sy_frame (X X' : Matrix (Fin d.m) (Fin d.n) (AE F E)) : sy d (X * (yy d)ᵀ) (X' * (yy d)ᵀ) = 0 := by
  have h : (yy d)ᵀ * dbl (incM F d.Y.J) * (yy d).map (cA σ) = 0 := by
    rw [yy, cA_incM, ← incM_dbl, ← incM_transpose, ← incM_mul, ← incM_mul, frame_iso, incM_zero']
  simp only [sy, symp]
  rw [hTens_outer _ _ _ _ _ _ _ h, mul_zero, map_zero]

def xs (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : Matrix (Fin d.m) (Fin d.n) (AE F E) :=
  (w * (incM F (d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E).1)ᵀ).toCols₂

theorem xs_add (w w' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : xs d (w + w') = xs d w + xs d w' := by
  ext i j; simp [xs, Matrix.add_mul, Matrix.toCols₂]

theorem xs_smul (a : AF F) (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : xs d (a • w) = a • xs d w := by
  ext i j; simp [xs, Matrix.smul_mul, Matrix.toCols₂]

theorem decomp (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    ∃ Z : Matrix (Fin d.m) (Fin d.n) (AE F E), w = Z * (dg d)ᵀ + xs d w * (yy d)ᵀ := by
  obtain ⟨t, ht⟩ := d.ok.frame.2
  set V := w * (incM F (d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E).1)ᵀ with hV
  have h1 : w = V * (incM F d.b.1)ᵀ := by
    rw [hV, Matrix.mul_assoc, ← Matrix.transpose_mul, ← incM_mul, Units.mul_inv, incM_one', Matrix.transpose_one,
      Matrix.mul_one]
  have h2 : incM F d.b.1 = Matrix.fromCols (incM F d.b.1.toCols₁) (incM F d.b.1.toCols₂) := by
    ext i (j | j) <;> rfl
  refine ⟨V.toCols₁ * (incM F t.1)ᵀ, ?_⟩
  have h3 : xs d w = V.toCols₂ := rfl
  rw [h3]
  conv_lhs => rw [h1, h2, ← Matrix.fromCols_toCols V]
  have ht' : incM F d.b.1.toCols₁ = @HMul.hMul (Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E))
      (Matrix (Fin d.n) (Fin d.n) (AE F E)) (Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E))
      Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (diagCols (Fin d.n)) (incM F t.1) := by
    rw [ht, ← incM_diagCols (F := F) (E := E)]
    exact incM_mul _ _
  rw [Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows, ht', Matrix.transpose_mul, ← Matrix.mul_assoc]

theorem xs_frame (X : Matrix (Fin d.m) (Fin d.n) (AE F E)) : xs d (X * (yy d)ᵀ) = X := by
  have h1 : incM F (d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E).1 * yy d = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)).toCols₂ := by
    have : (d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E).1 * d.b.1.toCols₂ = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E).toCols₂ := by
      rw [← Units.inv_mul d.b]
      ext i j; simp [Matrix.mul_apply, Matrix.toCols₂]
    rw [yy, ← incM_mul, this]
    ext i j; simp [incM, Matrix.toCols₂, Matrix.one_apply]
  rw [xs, Matrix.mul_assoc, ← Matrix.transpose_mul, h1]
  ext i j
  simp [Matrix.toCols₂, Matrix.mul_apply, Matrix.one_apply]

theorem sy_split (w w' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    sy d w w' = sy d (xs d w * (yy d)ᵀ) w' - sy d (xs d w' * (yy d)ᵀ) w := by
  obtain ⟨Z, hZ⟩ := decomp d w
  obtain ⟨Z', hZ'⟩ := decomp d w'
  have a1 : sy d w w' = sy d (Z * (dg d)ᵀ) w' + sy d (xs d w * (yy d)ᵀ) w' := by
    conv_lhs => rw [hZ]
    rw [sy_add_left]
  have a2 : sy d (Z * (dg d)ᵀ) w' = sy d (Z * (dg d)ᵀ) (xs d w' * (yy d)ᵀ) := by
    conv_lhs => rw [hZ']
    rw [sy_add_right, sy_diag, zero_add]
  have a3 : sy d (xs d w' * (yy d)ᵀ) w = sy d (xs d w' * (yy d)ᵀ) (Z * (dg d)ᵀ) := by
    conv_lhs => rw [hZ]
    rw [sy_add_right, sy_frame, add_zero]
  rw [a1, a2, a3, sy_antisymm d (Z * (dg d)ᵀ)]
  ring

end Adp

end PositivityTheory.SiegelWeilFormula.TBij

end
