import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.SigmaFiniteOfUnfold
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpOrbOfAmpDD
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaContOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselNeZeroOfCyclicOrbit

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

section Defs

variable {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp]

def aVec (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp))
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w0 v : H) (ξ : Wp)
    (t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (p1 : Mt k r × Mt k r) : Wp :=
  (psi k r z c (Matrix.of p1.2) * ⟪v, σ ((Matrix.of p1.1)⁻¹ * (Matrix.of p1.2)⁻¹ * t) w0⟫_ℂ) •
    π (Matrix.of p1.1) ξ

end Defs

def Psi (L : LocBessel k r) (w0 v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (p : PairSp k r) (x : Mt k r) :
    L.Wq →L[ℂ] L.Wp :=
  (innerSL ℂ (aVec L.z' L.c L.π' L.σ w0 v' ξ' (Matrix.of x) p.2)).smulRight
    (aVec L.z L.c L.π L.σ w0 v ξ (γ * Matrix.of x) p.1)

def InPair (L : LocBessel k r) (p : PairSp k r) : Prop :=
  Matrix.of p.1.1 ∈ UWset k r L.z ∧ Matrix.of p.1.2 ∈ Nset k r ∧ Matrix.of p.2.1 ∈ UWset k r L.z' ∧
    Matrix.of p.2.2 ∈ Nset k r

theorem uh_of_uw {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : h ∈ UH (Hpk k r) := hh.1

theorem uh_of_n {n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hn : n ∈ Nset k r) :
    n ∈ UH (Hpk k r) := hn.1

theorem Psi_eq (L : LocBessel k r) (w0 v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (p : PairSp k r) (x : Mt k r) :
    Psi L w0 v v' ξ ξ' γ p x =
      ((psi k r L.z L.c (Matrix.of p.1.2) * star (psi k r L.z' L.c (Matrix.of p.2.2))) *
        (⟪v, L.σ ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of x) w0⟫_ℂ *
          star ⟪v', L.σ ((Matrix.of p.2.1)⁻¹ * (Matrix.of p.2.2)⁻¹ * Matrix.of x) w0⟫_ℂ)) •
        (innerSL ℂ (L.π' (Matrix.of p.2.1) ξ')).smulRight (L.π (Matrix.of p.1.1) ξ) := by
  ext η'
  simp only [Psi, aVec, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, _root_.smul_apply,
    inner_smul_left, starRingEnd_apply, star_mul', smul_smul, Matrix.mul_assoc]
  congr 1
  ring

theorem schur_step (L : LocBessel k r) {μG : Measure (Mt k r)}
    (hμG : PI.BesselPeriodGGP.IsHaarOn (UH (Hpk k r)) μG) {d : ℝ} (hd : 0 < d)
    (hSch : ∀ v w v' w' : L.Hs,
      Integrable (fun x : Mt k r => ⟪w, L.σ (Matrix.of x) v⟫_ℂ * star ⟪w', L.σ (Matrix.of x) v'⟫_ℂ) μG ∧
      ∫ x, ⟪w, L.σ (Matrix.of x) v⟫_ℂ * star ⟪w', L.σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ))
    {w0 : L.Hs} (hw1 : ⟪w0, w0⟫_ℂ = 1) (v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
    {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r))
    {p : PairSp k r} (hp : InPair L p) :
    Integrable (fun x => Psi L w0 v v' ξ ξ' γ p x) μG ∧
      ∫ x, Psi L w0 v v' ξ ξ' γ p x ∂μG =
        ((d : ℂ))⁻¹ • besselIntg L (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' ξ ξ') γ p := by
  obtain ⟨hh, hn, hh', hn'⟩ := hp
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  have hhU := uh_of_uw hh
  have hnU := uh_of_n hn
  have hh'U := uh_of_uw hh'
  have hn'U := uh_of_n hn'
  have hhi := Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hhU
  have hni := Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hnU
  have hh'i := Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hh'U
  have hn'i := Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hn'U
  set A := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ with hA
  set B := (Matrix.of p.2.1)⁻¹ * (Matrix.of p.2.2)⁻¹ with hB
  set M := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of p.2.2 * Matrix.of p.2.1 with hM
  have hAU : A ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hhi hni) hγ
  have hBU : B ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hh'i hn'i
  have hMU : M ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hAU hn'U) hh'U
  have hMB : M * B = A := by
    rw [hM, hB, hA]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Matrix.of p.2.1) (Matrix.of p.2.1)⁻¹, (Formalism.FourierDecayAlt.P.S3dx6.unit_of_uh hh'U).1,
      Matrix.one_mul, (Formalism.FourierDecayAlt.P.S3dx6.unit_of_uh hn'U).1, Matrix.mul_one]

  let F : Mt k r → ℂ := fun y => ⟪L.σ M⁻¹ v, L.σ (Matrix.of y) w0⟫_ℂ * star ⟪v', L.σ (Matrix.of y) w0⟫_ℂ
  obtain ⟨hFi, hFe⟩ := hSch w0 (L.σ M⁻¹ v) w0 v'
  have hFe' : ∫ y, F y ∂μG = ⟪v, L.σ M v'⟫_ℂ / (d : ℂ) := by
    show ∫ y, ⟪L.σ M⁻¹ v, L.σ (Matrix.of y) w0⟫_ℂ * star ⟪v', L.σ (Matrix.of y) w0⟫_ℂ ∂μG = _
    rw [hFe, hw1, one_mul, ← Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_inner hσ hMU v v']
  have hlm : Measurable (lmulM (k := k) (r := r) B) :=
    Formalism.FourierDecayAlt.P.B7.meas_mulM (f := fun _ => ((B : Matrix _ _ ℂ) : Mt k r)) measurable_const measurable_id
  have hmp : MeasurePreserving (lmulM (k := k) (r := r) B) μG μG := ⟨hlm, hμG.2.2.2 B hBU⟩
  have hae : ∀ᵐ x ∂μG, Matrix.of x ∈ UH (Hpk k r) := Formalism.MainNotions.S.Pv.AmpDDPf.ae_mem_sk hμG
  have hfeq : ∀ᵐ x ∂μG, ⟪v, L.σ (A * Matrix.of x) w0⟫_ℂ * star ⟪v', L.σ (B * Matrix.of x) w0⟫_ℂ =
      F (lmulM B x) := by
    filter_upwards [hae] with x hx
    have hBx : B * Matrix.of x ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hBU hx
    have e1 : L.σ (A * Matrix.of x) = (L.σ M).comp (L.σ (B * Matrix.of x)) := by
      rw [← hMB, Matrix.mul_assoc]
      exact Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul hσ hMU hBx
    show _ = ⟪L.σ M⁻¹ v, L.σ (B * Matrix.of x) w0⟫_ℂ * star ⟪v', L.σ (B * Matrix.of x) w0⟫_ℂ
    rw [e1, ContinuousLinearMap.comp_apply, Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_inner hσ hMU]
  have hfi : Integrable (fun x : Mt k r =>
      ⟪v, L.σ (A * Matrix.of x) w0⟫_ℂ * star ⟪v', L.σ (B * Matrix.of x) w0⟫_ℂ) μG := by
    have h1 : Integrable (F ∘ lmulM B) μG := (hmp.integrable_comp hFi.aestronglyMeasurable).mpr hFi
    exact h1.congr (hfeq.mono fun x hx => hx.symm)
  have hfint : ∫ x, ⟪v, L.σ (A * Matrix.of x) w0⟫_ℂ * star ⟪v', L.σ (B * Matrix.of x) w0⟫_ℂ ∂μG =
      ⟪v, L.σ M v'⟫_ℂ / (d : ℂ) := by
    rw [integral_congr_ae hfeq, ← hFe']
    exact (integral_map hlm.aemeasurable (by rw [hmp.map_eq]; exact hFi.aestronglyMeasurable)).symm.trans
      (by rw [hmp.map_eq])

  set c : ℂ := psi k r L.z L.c (Matrix.of p.1.2) * star (psi k r L.z' L.c (Matrix.of p.2.2)) with hc
  set K : L.Wq →L[ℂ] L.Wp :=
    (innerSL ℂ (L.π' (Matrix.of p.2.1) ξ')).smulRight (L.π (Matrix.of p.1.1) ξ) with hK
  have hPsi : (fun x => Psi L w0 v v' ξ ξ' γ p x) = fun x : Mt k r =>
      (c * (⟪v, L.σ (A * Matrix.of x) w0⟫_ℂ * star ⟪v', L.σ (B * Matrix.of x) w0⟫_ℂ)) • K := by
    funext x
    rw [Psi_eq]
  refine ⟨?_, ?_⟩
  · rw [hPsi]
    exact (hfi.const_mul c).smul_const K
  · rw [hPsi, integral_smul_const, integral_const_mul, hfint]
    ext η'
    have hpi : ⟪ξ', L.π' (Matrix.of p.2.1)⁻¹ η'⟫_ℂ = ⟪L.π' (Matrix.of p.2.1) ξ', η'⟫_ℂ := by
      rw [Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_inner L.hz'.2 L.hπ' (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hh').1,
        Formalism.FourierDecayAlt.P.S3dx6.inv_inv_uh hh'U]
    simp only [hK, besselIntg, Formalism.MainNotions.S.Pv.AmpDD.coefF, _root_.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      ContinuousLinearMap.map_smul, smul_smul, hpi]
    congr 1
    rw [← hM]
    have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp
    ring

end Formalism.MainNotions.S.Pv.AmpDDPf
