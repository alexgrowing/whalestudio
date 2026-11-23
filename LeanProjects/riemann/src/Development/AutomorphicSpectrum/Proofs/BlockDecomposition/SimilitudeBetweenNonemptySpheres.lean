import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm
import Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint
import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SimilExists

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def frame (σ : E →ₐ[F] E) (J : Matrix (Fin 2) (Fin 2) E) (x : Fin 2 → E) : Matrix (Fin 2) (Fin 2) E :=
  !![x 0, -(σ (x 0) * J 0 1 + σ (x 1) * J 1 1); x 1, σ (x 0) * J 0 0 + σ (x 1) * J 1 0]

theorem frame_det (σ : E →ₐ[F] E) (J : Matrix (Fin 2) (Fin 2) E) (x : Fin 2 → E) :
    (frame σ J x).det = hE σ J x x := by
  simp [frame, Matrix.det_fin_two, hE, hform, Fin.sum_univ_two]
  ring

theorem frame_gram {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) {J : Matrix (Fin 2) (Fin 2) E}
    (hJ : IsHermND σ J) (x : Fin 2 → E) :
    cT (σ : E →+* E) (frame σ J x) * J * frame σ J x =
      hE σ J x x • Matrix.diagonal ![1, J.det] := by
  have h00 : σ (J 0 0) = J 0 0 := hJ.1 0 0
  have h11 : σ (J 1 1) = J 1 1 := hJ.1 1 1
  have h01 : σ (J 1 0) = J 0 1 := hJ.1 0 1
  have h10 : σ (J 0 1) = J 1 0 := hJ.1 1 0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frame, cT, Matrix.mul_apply, Fin.sum_univ_two, hE, hform, Matrix.det_fin_two, hσ, h00, h11,
      h01, h10] <;> ring

theorem exists_similitude_of_vectors {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e)
    {J : Matrix (Fin 2) (Fin 2) E} (hJ : IsHermND σ J) {x x' : Fin 2 → E} {b b' : E}
    (hx : hE σ J x x = b) (hx' : hE σ J x' x' = b') (hb : b ≠ 0) (hb' : b' ≠ 0) :
    ∃ γ : GL (Fin 2) E, cT (σ : E →+* E) (γ : Matrix (Fin 2) (Fin 2) E) * J *
      (γ : Matrix (Fin 2) (Fin 2) E) = (b' / b) • J := by
  set P := frame σ J x with hP
  set P' := frame σ J x' with hP'
  have hdet : P.det = b := by rw [hP, frame_det, hx]
  have hdet' : P'.det = b' := by rw [hP', frame_det, hx']
  have hu : IsUnit P.det := by rw [hdet]; exact hb.isUnit
  have hinv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hu
  have hc : cT (σ : E →+* E) P⁻¹ * cT (σ : E →+* E) P = 1 := by
    rw [← cT_mul, hinv, cT_one]
  have hg : cT (σ : E →+* E) P * J * P = b • Matrix.diagonal ![1, J.det] := by
    rw [hP, frame_gram hσ hJ, hx]
  have hg' : cT (σ : E →+* E) P' * J * P' = b' • Matrix.diagonal ![1, J.det] := by
    rw [hP', frame_gram hσ hJ, hx']
  have hJ' : J = b • (cT (σ : E →+* E) P⁻¹ * Matrix.diagonal ![1, J.det] * P⁻¹) := by
    calc J = (cT (σ : E →+* E) P⁻¹ * cT (σ : E →+* E) P) * J * (P * P⁻¹) := by
          rw [hc, hinv, Matrix.one_mul, Matrix.mul_one]
      _ = cT (σ : E →+* E) P⁻¹ * (cT (σ : E →+* E) P * J * P) * P⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hg, Matrix.mul_smul, Matrix.smul_mul]
  have hdetG : (P' * P⁻¹).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, hdet', hdet]
    simpa using ⟨hb', hb⟩
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (P' * P⁻¹) hdetG, ?_⟩
  change cT (σ : E →+* E) (P' * P⁻¹) * J * (P' * P⁻¹) = (b' / b) • J
  calc cT (σ : E →+* E) (P' * P⁻¹) * J * (P' * P⁻¹)
      = cT (σ : E →+* E) P⁻¹ * (cT (σ : E →+* E) P' * J * P') * P⁻¹ := by
        rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = b' • (cT (σ : E →+* E) P⁻¹ * Matrix.diagonal ![1, J.det] * P⁻¹) := by
        rw [hg', Matrix.mul_smul, Matrix.smul_mul]
    _ = (b' / b) • (b • (cT (σ : E →+* E) P⁻¹ * Matrix.diagonal ![1, J.det] * P⁻¹)) := by
        rw [smul_smul, div_mul_cancel₀ _ hb]
    _ = (b' / b) • J := by rw [← hJ']

theorem exists_similitude : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ J : Matrix (Fin 2) (Fin 2) E, IsHermND σ J → ∀ β β' : F, β ≠ 0 → β' ≠ 0 → (PositivityTheory.Rg.Mass.sph σ J β).Nonempty → (PositivityTheory.Rg.Mass.sph σ J β').Nonempty → ∃ γ : GL (Fin 2) E, cT (σ : E →+* E) (γ : Matrix (Fin 2) (Fin 2) E) * J * (γ : Matrix (Fin 2) (Fin 2) E) = (algebraMap F E (β' / β)) • J := by
  intro F E _ _ _ _ _ σ hcm J hJ β β' hβ hβ' ⟨X, hX⟩ ⟨X', hX'⟩
  have hσ : ∀ e, σ (σ e) = e := fun e => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hcm.2.2.2, hcm.2.2.2]
    simp
  have hx : hE σ J (X 0) (X 0) = algebraMap F E β := congrFun (congrFun hX 0) 0
  have hx' : hE σ J (X' 0) (X' 0) = algebraMap F E β' := congrFun (congrFun hX' 0) 0
  have hb : algebraMap F E β ≠ 0 := by simpa using hβ
  have hb' : algebraMap F E β' ≠ 0 := by simpa using hβ'
  rw [map_div₀]
  exact exists_similitude_of_vectors hσ hJ hx hx' hb hb'

end GlobalTheory.CompanionTheory.SimilExists

end
