import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RootCoordinatesIndex

noncomputable section

open scoped Classical
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf
open scoped ENNReal

namespace Formalism.L2.SG.RealConjugatorData

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def toUJn {n : ℕ} {ε : Fin n → Bool} (M : Matrix (Fin n) (Fin n) ℂ) (hM : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε) :
    Formalism.REAL.UJ ε :=
  ⟨⟨M, Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε,
    (mul_eq_one_comm_of_card_eq (Fin n) (Fin n) ℂ rfl).mp (by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM, Formalism.REAL.Jm_mul_self]),
    by rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM, Formalism.REAL.Jm_mul_self]⟩, hM⟩

theorem uMat_toUJn {n : ℕ} {ε : Fin n → Bool} (M : Matrix (Fin n) (Fin n) ℂ) (hM : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε) :
    uMat (toUJn M hM) = M := rfl

theorem uMat_inv' {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : uMat g⁻¹ = (uMat g)⁻¹ := by
  show (((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
    (((g : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)⁻¹
  rw [Subgroup.coe_inv, Matrix.coe_units_inv]

theorem uMat_mul_inv {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : uMat g * (uMat g)⁻¹ = 1 := by
  rw [← uMat_inv']
  show (((g : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
    (((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1
  rw [Subgroup.coe_inv, Units.mul_inv]

theorem uMat_inv_mul {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : (uMat g)⁻¹ * uMat g = 1 := by
  rw [← uMat_inv']
  show (((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
    (((g : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1
  rw [Subgroup.coe_inv, Units.inv_mul]

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (γ : X.B.I.Ginf) (τ : D.what₂.Tau)

local notation "NN" => 2 * D.R.rS + D.R.k + 1

def cMr (y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  (C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat y * (uMat (γ (vOf X τ)) * C.Q τ) : Matrix (Fin NN) (Fin NN) ℂ)

theorem cMr_eq (y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    (cMr C γ τ y : Matrix (Fin NN) (Fin NN) ℂ) = Formalism.L2.SG.RealFrameCoordinates.cMg C γ τ y := by
  show C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat y * (uMat (γ (vOf X τ)) * C.Q τ) =
    C.Qi τ * ((uMat (γ (vOf X τ)))⁻¹ * uMat y * uMat (γ (vOf X τ))) * C.Q τ
  simp only [Matrix.mul_assoc]

theorem cMr_closedEmb : Topology.IsClosedEmbedding (cMr C γ τ) := by
  obtain ⟨hQiQ, hQQi, _, _⟩ := C.isT τ
  set g := uMat (γ (vOf X τ))
  have h1 : g * g⁻¹ = 1 := uMat_mul_inv _
  have h2 : g⁻¹ * g = 1 := uMat_inv_mul _
  let L : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ ≃ₜ Matrix (Fin NN) (Fin NN) ℂ :=
    { toFun := fun M => C.Qi τ * g⁻¹ * M * (g * C.Q τ)
      invFun := fun M => g * C.Q τ * M * (C.Qi τ * g⁻¹)
      left_inv := fun M => by
        show g * C.Q τ * (C.Qi τ * g⁻¹ * M * (g * C.Q τ)) * (C.Qi τ * g⁻¹) = M
        calc g * C.Q τ * (C.Qi τ * g⁻¹ * M * (g * C.Q τ)) * (C.Qi τ * g⁻¹)
            = g * (C.Q τ * C.Qi τ) * g⁻¹ * M * (g * (C.Q τ * C.Qi τ) * g⁻¹) := by simp only [Matrix.mul_assoc]
          _ = M := by rw [hQQi, Matrix.mul_one, h1, Matrix.one_mul, Matrix.mul_one]
      right_inv := fun M => by
        show C.Qi τ * g⁻¹ * (g * C.Q τ * M * (C.Qi τ * g⁻¹)) * (g * C.Q τ) = M
        calc C.Qi τ * g⁻¹ * (g * C.Q τ * M * (C.Qi τ * g⁻¹)) * (g * C.Q τ)
            = C.Qi τ * (g⁻¹ * g) * C.Q τ * M * (C.Qi τ * (g⁻¹ * g) * C.Q τ) := by simp only [Matrix.mul_assoc]
          _ = M := by rw [h2, Matrix.mul_one, hQiQ, Matrix.one_mul, Matrix.mul_one]
      continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
  exact L.isClosedEmbedding.comp ((Formalism.REAL.isClosedEmbeddingMatrix _ (X.B.I.ε (vOf X τ))).1)

theorem cMr_measEmb : MeasurableEmbedding (cMr C γ τ) := (cMr_closedEmb C γ τ).measurableEmbedding

variable (u u' : D.what₂.Word)

theorem conjugator_inverse : (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (γ (vOf X τ)))⁻¹ =
    C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * C.Q τ := by
  obtain ⟨hQiQ, hQQi, _, _⟩ := C.isT τ
  refine Matrix.inv_eq_right_inv ?_
  show C.Qi τ * uMat (γ (vOf X τ)) * C.Q τ * (C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * C.Q τ) = 1
  calc C.Qi τ * uMat (γ (vOf X τ)) * C.Q τ * (C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * C.Q τ)
      = C.Qi τ * (uMat (γ (vOf X τ)) * (C.Q τ * C.Qi τ) * (uMat (γ (vOf X τ)))⁻¹) * C.Q τ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hQQi, Matrix.mul_one, uMat_mul_inv, Matrix.mul_one, hQiQ]

theorem stV_iff (y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    y ∈ Formalism.L2.SG.NGPin.StV X u u' γ (vOf X τ) ↔
      (cMr C γ τ y : Matrix (Fin NN) (Fin NN) ℂ) ∈ Formalism.MainNotions.S.Rset D.R.k D.R.rS (Formalism.L2.SG.RealFrameCoordinates.g0 C γ τ) := by
  obtain ⟨hQiQ, hQQi, _, _⟩ := C.isT τ
  have hy : (uMat y)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * uMat y = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := y.2
  have hy' : (uMat ((γ (vOf X τ))⁻¹ * y * γ (vOf X τ)))ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) *
      uMat ((γ (vOf X τ))⁻¹ * y * γ (vOf X τ)) = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := ((γ (vOf X τ))⁻¹ * y * γ (vOf X τ)).2
  have h1 := Formalism.L2.SG.RootCoordinatesIndex.inN_iff (C := C) (τ := τ) _ (Formalism.L2.SG.Pf.zTr C u τ).1 _ hy
  have h2 := Formalism.L2.SG.RootCoordinatesIndex.inN_iff (C := C) (τ := τ) _ (Formalism.L2.SG.Pf.zTr C u' τ).1 _ hy'
  have e2 : C.Qi τ * uMat ((γ (vOf X τ))⁻¹ * y * γ (vOf X τ)) * C.Q τ = (cMr C γ τ y : Matrix (Fin NN) (Fin NN) ℂ) := by
    rw [cMr_eq]
    unfold Formalism.L2.SG.RealFrameCoordinates.cMg
    rw [show uMat ((γ (vOf X τ))⁻¹ * y * γ (vOf X τ)) = uMat ((γ (vOf X τ))⁻¹) * uMat y * uMat (γ (vOf X τ)) from rfl,
      uMat_inv']
  have e1 : Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (γ (vOf X τ)) * Matrix.of (cMr C γ τ y) *
      (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (γ (vOf X τ)))⁻¹ = C.Qi τ * uMat y * C.Q τ := by
    rw [conjugator_inverse]
    show C.Qi τ * uMat (γ (vOf X τ)) * C.Q τ * (C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat y * (uMat (γ (vOf X τ)) * C.Q τ)) *
      (C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * C.Q τ) = C.Qi τ * uMat y * C.Q τ
    calc _ = C.Qi τ * (uMat (γ (vOf X τ)) * (C.Q τ * C.Qi τ) * (uMat (γ (vOf X τ)))⁻¹) * uMat y *
          (uMat (γ (vOf X τ)) * (C.Q τ * C.Qi τ) * (uMat (γ (vOf X τ)))⁻¹) * C.Q τ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hQQi, Matrix.mul_one, uMat_mul_inv, Matrix.mul_one, Matrix.mul_one]
  show (Formalism.L2.SG.HidaSetting.InN _ _ _ (uMat y) ∧ Formalism.L2.SG.HidaSetting.InN _ _ _ (uMat ((γ (vOf X τ))⁻¹ * y * γ (vOf X τ)))) ↔ _
  rw [h1, h2, e2]
  constructor
  · rintro ⟨ha, hb⟩
    refine ⟨hb, ?_⟩
    convert ha using 1
    exact e1
  · rintro ⟨hb, ha⟩
    refine ⟨?_, hb⟩
    convert ha using 1
    exact e1.symm

theorem rset_range (m : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)
    (hm : Matrix.of m ∈ Formalism.MainNotions.S.Rset D.R.k D.R.rS (Formalism.L2.SG.RealFrameCoordinates.g0 C γ τ)) :
    m ∈ Set.range (cMr C γ τ) := by
  obtain ⟨hQiQ, hQQi, hH, _⟩ := C.isT τ
  have hmU : (Matrix.of m)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * Matrix.of m = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hm.1.1
  have hgi0 : (uMat (γ (vOf X τ))⁻¹)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * uMat (γ (vOf X τ))⁻¹ =
      Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := ((γ (vOf X τ))⁻¹).2
  rw [uMat_inv'] at hgi0
  set g := uMat (γ (vOf X τ))
  have hg : gᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * g = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := (γ (vOf X τ)).2
  have hgi : (g⁻¹)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * g⁻¹ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := hgi0
  have hQi : (C.Qi τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.Qi τ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
    rw [← hH]
    calc (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * C.Qi τ
        = (C.Q τ * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.Qi τ) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hQQi, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  set M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ := g * C.Q τ * Matrix.of m * C.Qi τ * g⁻¹ with hM
  have hMU : Mᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * M = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
    calc Mᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * M
        = (g⁻¹)ᴴ * ((C.Qi τ)ᴴ * ((Matrix.of m)ᴴ * ((C.Q τ)ᴴ *
            (gᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * g) * C.Q τ) * Matrix.of m) * C.Qi τ) * g⁻¹ := by
          rw [hM]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hg, hH, hmU, hQi, hgi]
  have h2 : g⁻¹ * g = 1 := uMat_inv_mul _
  refine ⟨toUJn M hMU, ?_⟩
  show C.Qi τ * g⁻¹ * M * (g * C.Q τ) = Matrix.of m
  rw [hM]
  calc C.Qi τ * g⁻¹ * (g * C.Q τ * Matrix.of m * C.Qi τ * g⁻¹) * (g * C.Q τ)
      = (C.Qi τ * (g⁻¹ * g) * C.Q τ) * Matrix.of m * (C.Qi τ * (g⁻¹ * g) * C.Q τ) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.of m := by rw [h2, Matrix.mul_one, hQiQ, Matrix.one_mul, Matrix.mul_one]

end Formalism.L2.SG.RealConjugatorData

end
