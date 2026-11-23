import Formalism.HermitianCurvature.LemmaDensOfSteps
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LduDecompositionExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isLowUni_mul isLowUni_det)

theorem unitriangular_eq_one_of_minors_nonzero {m : ℕ} {Z u u' : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) (hu' : u' ∈ C2.UTset m)
    (h : uᴴ * Z * u' = Z)
    (hZ : ∀ (l : ℕ) (hl : l ≤ m), (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det ≠ 0) : u = 1 := by
  obtain ⟨L, U, d, hL, hU, e⟩ := S3x7.ldu_exists m Z (fun l hl => isUnit_iff_ne_zero.mpr (hZ l hl.le))
  have hUp : IsUpUni u' := S3x7.mk_up (fun i j hij => hu'.1 i j hij) hu'.2
  have hLow : IsLowUni uᴴ := S3x7.mk_low (fun i j hij => by simp [Matrix.conjTranspose_apply, hu.1 j i hij])
    (fun i => by simp [Matrix.conjTranspose_apply, hu.2 i])
  have e2 : L * diagonal d * U = (uᴴ * L) * diagonal d * (U * u') := by
    calc L * diagonal d * U = Z := e.symm
      _ = uᴴ * Z * u' := h.symm
      _ = _ := by rw [e]; simp only [Matrix.mul_assoc]
  have hd : S3.lead (L * diagonal d * U) m le_rfl ∈ nonZeroDivisors ℂ := by
    rw [← e]; exact mem_nonZeroDivisors_of_ne_zero (hZ m le_rfl)
  obtain ⟨hLL, -, -⟩ := S3x7.ldu_unique hL hU (isLowUni_mul ℂ hLow hL) (isUpUni_mul ℂ hU hUp) hd e2
  have hLu : IsUnit L.det := by rw [isLowUni_det ℂ hL]; exact isUnit_one
  have hu1 : uᴴ = 1 := by
    have h1 := congrArg (· * L⁻¹) hLL
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hLu, Matrix.mul_one] at h1
    exact h1.symm
  have := congrArg Matrix.conjTranspose hu1
  simpa using this

theorem relevant_trivial_big_cell_of_parts : Formalism.FourierDecayAlt.DensityAveraging.RTrivBigOfParts := by
  intro h2 h3 k r Wp Wq _ _ _ _ _ D γ hγ hrel
  have hStd : C2.Std k r D.z D.z' := ⟨D.k_pos, ⟨D.z_mem, D.T_pos⟩, ⟨D.z'_mem, D.T'_pos⟩⟩
  have hPos : C2.PosPt k r D.z D.z' γ := ⟨hγ.1, hγ.2.1⟩
  have hγu : IsUnit γ.det := Dx2.OrbJ.isUnit_of_G hγ.1
  obtain ⟨_, hReq, _, _, _⟩ := h2 k r D.z D.z' γ hStd hPos
  obtain ⟨hbij, hinj, _⟩ := h3 k r D.z D.z' γ hStd hPos
  have hN1 : (1 : B.Mat k r) ∈ Nset k r := (unipotent_radical_closed k r).one_mem
  have hconj : ∀ ρ : B.Mat k r, γ * (γ⁻¹ * ρ * γ) * γ⁻¹ = ρ := by
    intro ρ
    simp [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hγu, Matrix.mul_nonsing_inv_cancel_left _ _ hγu]
  have mem : ∀ ρ ∈ Rset γ, ρ ∈ C2.Rst k r D.z D.z' γ := by
    intro ρ hρ
    rw [hReq]
    exact ⟨hρ.1, γ⁻¹ * ρ * γ, hρ.2, (hconj ρ).symm⟩
  have one_R : (1 : B.Mat k r) ∈ Rset γ := ⟨hN1, by simpa [Matrix.nonsing_inv_mul _ hγu] using hN1⟩
  have hZ : ∀ (l : ℕ) (hl : l ≤ r + 1),
      ((Zhat k r D.z D.z' γ).submatrix (Fin.castLE hl) (Fin.castLE hl)).det ≠ 0 :=
    fun l hl => hγ.2.2 ⟨l, by omega⟩ (Finset.mem_univ _)
  have huOne : ∀ x ∈ C2.Rst k r D.z D.z' γ, C2.uMap k r D.z x = 1 := by
    intro x hx
    obtain ⟨h1, h2', h3'⟩ := hbij.mapsTo hx
    exact unitriangular_eq_one_of_minors_nonzero h1 h2' h3' hZ
  ext ρ
  constructor
  · intro hρ
    exact hinj (mem ρ hρ) (mem 1 one_R) ((huOne ρ (mem ρ hρ)).trans (huOne 1 (mem 1 one_R)).symm)
  · intro hρ
    rw [Set.mem_singleton_iff.mp hρ]
    exact one_R

end Formalism.FourierDecayAlt.P
