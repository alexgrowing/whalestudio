import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.UnipotentLeDiagonalStabiliser
import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldB

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

set_option linter.unusedSectionVars false

namespace PositivityTheory.SiegelWeilFormula.kunf

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E}

def jw {R : Type} [CommRing R] (n : ℕ) (e : R) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  Matrix.fromBlocks 0 1 (e • 1) 0

theorem incM_mul' {α β γ : Type} [Fintype β] (A : Matrix α β E) (C : Matrix β γ E) :
    incM F (A * C) = incM F A * incM F C := Matrix.map_mul

theorem incM_transpose' {α β : Type} (A : Matrix α β E) : incM F Aᵀ = (incM F A)ᵀ := rfl

theorem incM_map_cA {α β : Type} (A : Matrix α β E) : (incM F A).map (cA σ) = incM F (A.map σ) := by
  ext i j; exact GlobalTheory.EisBL.DoubledUnipotentRadical.cA_inclR σ (A i j)

theorem map_cA_mul {α β γ : Type} [Fintype β] (A : Matrix α β (AE F E)) (C : Matrix β γ (AE F E)) :
    (A * C).map (cA σ) = A.map (cA σ) * C.map (cA σ) := Matrix.map_mul (f := (cA σ).toRingHom)

theorem incM_dbl (J : Matrix (Fin n) (Fin n) E) : incM F (dbl J) = dbl (incM F J) := by
  ext (i | i) (j | j) <;> simp [incM, dbl]

theorem incM_jw (e : E) : incM F (jw n e) = jw n (inclR (F := F) (AF F) e) := by
  ext (i | i) (j | j) <;> simp [incM, jw, Matrix.one_apply] <;> split_ifs <;> simp

theorem incM_frame {ε : ℤˣ} (hε : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    (incM F b.1)ᵀ * dbl (incM F Y.J) * (incM F b.1).map (cA σ) = jw n (((ε : ℤ) : AE F E)) := by
  have h := congrArg (incM F) hε
  rw [incM_mul', incM_mul', incM_dbl, ← incM_map_cA] at h
  rw [← incM_transpose', h, show Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 = jw n ((ε : ℤ) : E) from rfl, incM_jw,
    map_intCast]

theorem frame_eq {ε : ℤˣ} (hε : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (x : G2 σ Y) :
    (inFrame b x)ᵀ * jw n (((ε : ℤ) : AE F E)) * (inFrame b x).map (cA σ) = jw n (((ε : ℤ) : AE F E)) := by
  have hJ := incM_frame (F := F) hε
  set B0 := incM F b.1
  set Bi := incM F (b⁻¹).1
  set D := dbl (incM F Y.J)
  have hX : (mat2 x)ᵀ * D * (mat2 x).map (cA σ) = D := x.2
  have h2 : B0.map (cA σ) * Bi.map (cA σ) = 1 := by
    rw [← map_cA_mul, GlobalTheory.EisBL.DoubledParabolic.incM_mul_inv b]; ext i j; simp [Matrix.one_apply]
  have h3 : Biᵀ * B0ᵀ = 1 := by rw [← Matrix.transpose_mul, GlobalTheory.EisBL.DoubledParabolic.incM_mul_inv b, Matrix.transpose_one]
  show (Bi * mat2 x * B0)ᵀ * _ * (Bi * mat2 x * B0).map (cA σ) = _
  rw [← hJ, Matrix.transpose_mul, Matrix.transpose_mul, map_cA_mul, map_cA_mul]
  calc B0ᵀ * ((mat2 x)ᵀ * Biᵀ) * (B0ᵀ * D * B0.map (cA σ)) * (Bi.map (cA σ) * (mat2 x).map (cA σ) * B0.map (cA σ))
      = B0ᵀ * ((mat2 x)ᵀ * (Biᵀ * B0ᵀ) * D * (B0.map (cA σ) * Bi.map (cA σ)) * (mat2 x).map (cA σ)) * B0.map (cA σ) := by
        simp only [Matrix.mul_assoc]
    _ = B0ᵀ * D * B0.map (cA σ) := by
        rw [h3, h2, Matrix.mul_one, Matrix.mul_one, hX, Matrix.mul_assoc]

theorem exists_of_frame {ε : ℤˣ} (hε : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (M M' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) (h : M * M' = 1)
    (hM : Mᵀ * jw n (((ε : ℤ) : AE F E)) * M.map (cA σ) = jw n (((ε : ℤ) : AE F E))) :
    ∃ x : G2 σ Y, inFrame b x = M := by
  have hJ := incM_frame (F := F) hε
  set B0 := incM F b.1
  set Bi := incM F (b⁻¹).1
  set D := dbl (incM F Y.J)
  set J := jw n (((ε : ℤ) : AE F E))
  have h' : M' * M = 1 := mul_eq_one_comm.1 h
  have e1 : B0 * Bi = 1 := GlobalTheory.EisBL.DoubledParabolic.incM_mul_inv b
  have e2 : Bi * B0 = 1 := GlobalTheory.EisBL.DoubledParabolic.incM_inv_mul b
  have h2 : B0.map (cA σ) * Bi.map (cA σ) = 1 := by
    rw [← map_cA_mul, e1]; ext i j; simp [Matrix.one_apply]
  have h2' : Bi.map (cA σ) * B0.map (cA σ) = 1 := by
    rw [← map_cA_mul, e2]; ext i j; simp [Matrix.one_apply]
  have h3 : Biᵀ * B0ᵀ = 1 := by rw [← Matrix.transpose_mul, e1, Matrix.transpose_one]
  have h3' : B0ᵀ * Biᵀ = 1 := by rw [← Matrix.transpose_mul, e2, Matrix.transpose_one]
  have hD : D = Biᵀ * J * Bi.map (cA σ) := by
    rw [← hJ]
    calc D = (Biᵀ * B0ᵀ) * D * (B0.map (cA σ) * Bi.map (cA σ)) := by rw [h3, h2, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  let U : GL (Fin n ⊕ Fin n) (AE F E) := ⟨B0 * M * Bi, B0 * M' * Bi, by
      calc B0 * M * Bi * (B0 * M' * Bi) = B0 * (M * (Bi * B0) * M') * Bi := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [e2, Matrix.mul_one, h, Matrix.mul_one, e1], by
      calc B0 * M' * Bi * (B0 * M * Bi) = B0 * (M' * (Bi * B0) * M) * Bi := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [e2, Matrix.mul_one, h', Matrix.mul_one, e1]⟩
  have hU : U ∈ UG (cA σ) D := by
    show (B0 * M * Bi)ᵀ * D * (B0 * M * Bi).map (cA σ) = D
    rw [hD, Matrix.transpose_mul, Matrix.transpose_mul, map_cA_mul, map_cA_mul]
    calc Biᵀ * (Mᵀ * B0ᵀ) * (Biᵀ * J * Bi.map (cA σ)) * (B0.map (cA σ) * M.map (cA σ) * Bi.map (cA σ))
        = Biᵀ * (Mᵀ * (B0ᵀ * Biᵀ) * J * (Bi.map (cA σ) * B0.map (cA σ)) * M.map (cA σ)) * Bi.map (cA σ) := by
          simp only [Matrix.mul_assoc]
      _ = Biᵀ * J * Bi.map (cA σ) := by
          rw [h3', h2', Matrix.mul_one, Matrix.mul_one, hM, Matrix.mul_assoc]
  refine ⟨⟨U, hU⟩, ?_⟩
  show Bi * (B0 * M * Bi) * B0 = M
  calc Bi * (B0 * M * Bi) * B0 = (Bi * B0) * M * (Bi * B0) := by simp only [Matrix.mul_assoc]
    _ = M := by rw [e2, Matrix.one_mul, Matrix.mul_one]

theorem isPar_frame {t₀ : GL (Fin n) E} (ht₀ : b.1.toCols₁ = diagCols (E := E) (Fin n) * t₀.1) (p : G2 σ Y)
    (t : GL (Fin n) (AE F E)) :
    IsPar p t ↔ (inFrame b p).toBlocks₂₁ = 0 ∧ t.1 = incM F t₀.1 * (inFrame b p).toBlocks₁₁ * incM F (t₀⁻¹).1 := by
  set B0 := incM F b.1
  set Bi := incM F (b⁻¹).1
  set P := inFrame b p
  set T0 := incM F t₀.1
  set Ti := incM F (t₀⁻¹).1
  set e1 : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E) := Matrix.fromRows 1 0
  have e2 : Bi * B0 = 1 := GlobalTheory.EisBL.DoubledParabolic.incM_inv_mul b
  have e3 : B0 * Bi = 1 := GlobalTheory.EisBL.DoubledParabolic.incM_mul_inv b
  have hT : T0 * Ti = 1 := by
    show incM F t₀.1 * incM F (t₀⁻¹).1 = 1
    rw [← incM_mul', Units.mul_inv]; ext i j; simp [incM, Matrix.one_apply]
  have hT' : Ti * T0 = 1 := by
    show incM F (t₀⁻¹).1 * incM F t₀.1 = 1
    rw [← incM_mul', Units.inv_mul]; ext i j; simp [incM, Matrix.one_apply]
  have hmat : mat2 p = B0 * P * Bi := by
    show mat2 p = B0 * (Bi * mat2 p * B0) * Bi
    calc mat2 p = (B0 * Bi) * mat2 p * (B0 * Bi) := by rw [e3, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hcols : B0 * e1 = incM F b.1.toCols₁ := by
    ext i j
    simp [B0, e1, incM, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toCols₁]
  have hdc : diagCols (E := AE F E) (Fin n) = B0 * e1 * Ti := by
    rw [hcols, ht₀, incM_mul', incM_diag, Matrix.mul_assoc, hT, Matrix.mul_one]
  have cB : ∀ X : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E), Bi * (B0 * X) = X := fun X => by
    rw [← Matrix.mul_assoc, e2, Matrix.one_mul]
  have key : IsPar p t ↔ P * e1 = e1 * (Ti * t.1 * T0) := by
    show mat2 p * diagCols (E := AE F E) (Fin n) = diagCols (E := AE F E) (Fin n) * t.1 ↔ _
    rw [hmat, hdc]
    constructor
    · intro h
      simp only [Matrix.mul_assoc] at h
      rw [cB] at h
      have h1 : Bi * (B0 * (P * (e1 * Ti))) = Bi * (B0 * (e1 * (Ti * t.1))) := by rw [h]
      rw [cB, cB] at h1
      calc P * e1 = P * (e1 * Ti) * T0 := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hT', Matrix.mul_one]
        _ = e1 * (Ti * t.1) * T0 := by rw [h1]
        _ = e1 * (Ti * t.1 * T0) := by simp only [Matrix.mul_assoc]
    · intro h
      simp only [Matrix.mul_assoc]
      rw [cB, ← Matrix.mul_assoc P, h]
      simp only [Matrix.mul_assoc, hT, Matrix.mul_one]
  have hPe : P * e1 = Matrix.fromRows P.toBlocks₁₁ P.toBlocks₂₁ := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks P]
    simp [e1, Matrix.fromBlocks_mul_fromRows]
  have he : ∀ X : Matrix (Fin n) (Fin n) (AE F E), e1 * X = Matrix.fromRows X 0 := fun X => by
    simp [e1, Matrix.fromRows_mul]
  rw [key, hPe, he, Matrix.fromRows_ext_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    rw [h1]
    calc t.1 = (T0 * Ti) * t.1 * (T0 * Ti) := by rw [hT, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  · rintro ⟨h2, h1⟩
    refine ⟨?_, h2⟩
    rw [h1]
    calc P.toBlocks₁₁ = (Ti * T0) * P.toBlocks₁₁ * (Ti * T0) := by rw [hT', Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]

end PositivityTheory.SiegelWeilFormula.kunf

end
