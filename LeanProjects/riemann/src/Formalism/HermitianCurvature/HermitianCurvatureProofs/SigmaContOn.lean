import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace Formalism.FourierDecayAlt.P.S3dx4

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

def triv {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) : B.RealPlaceData k r ℂ ℂ where
  z := D.z
  z' := D.z'
  π := fun _ => 1
  π' := fun _ => 1
  μG := D.μG
  μW := D.μW
  μN := D.μN
  μW' := D.μW'
  μsec := D.μsec
  χ := D.χ
  k_pos := D.k_pos
  z_mem := D.z_mem
  z'_mem := D.z'_mem
  T_pos := D.T_pos
  T'_pos := D.T'_pos
  π_rep := ⟨rfl, fun _ _ _ _ => by ext; simp⟩
  π'_rep := ⟨rfl, fun _ _ _ _ => by ext; simp⟩
  π_unitary := fun _ _ v => by simp
  π'_unitary := fun _ _ v => by simp
  π_cont := continuousOn_const
  π'_cont := continuousOn_const
  haarG := D.haarG
  haarW := D.haarW
  haarN := D.haarN
  haarW' := D.haarW'
  sec := D.sec
  χ_smooth := D.χ_smooth
  χ_supp := D.χ_supp
  χ_int := D.χ_int

theorem hpk_eq (k r : ℕ) : PI.UpqRep.Hpk k r = Formalism.QuantumDeterminants.Hpk k r := rfl

theorem uh_eq (k r : ℕ) : PI.UpqRep.UH (PI.UpqRep.Hpk k r) = Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := rfl

theorem sigma_contOn {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (v : H) :
    ContinuousOn (fun g => σ g v) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
  obtain ⟨P, ⟨⟨hPu, hPJ⟩, hPunit⟩, hDS⟩ := hσ
  have hc := hDS.2.2.1.2.2 v
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have hmaps : Set.MapsTo (fun g : Mx k r => P * g * P⁻¹) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
      (PI.UpqRep.UJset ε) := by
    intro g hg
    show (P * g * P⁻¹)ᴴ * PI.UpqRep.Jm ε * (P * g * P⁻¹) = PI.UpqRep.Jm ε
    have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
    have hJ : (P⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * P⁻¹ = PI.UpqRep.Jm ε := by
      rw [← hpk_eq, ← hPJ]
      have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
      have h2 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
      calc (P⁻¹)ᴴ * (Pᴴ * PI.UpqRep.Jm ε * P) * P⁻¹
          = ((P⁻¹)ᴴ * Pᴴ) * PI.UpqRep.Jm ε * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
        _ = PI.UpqRep.Jm ε := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
    have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
    have hPPh : Pᴴ * (P⁻¹)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hPP, Matrix.conjTranspose_one]
    calc (P * g * P⁻¹)ᴴ * PI.UpqRep.Jm ε * (P * g * P⁻¹)
        = (P⁻¹)ᴴ * gᴴ * Pᴴ * ((P⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * P⁻¹) * (P * g * P⁻¹) := by
          rw [hJ]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (P⁻¹)ᴴ * (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g) * P⁻¹ := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Pᴴ (P⁻¹)ᴴ, hPPh, Matrix.one_mul]
          rw [← Matrix.mul_assoc P⁻¹ P, hPP, Matrix.one_mul]
      _ = PI.UpqRep.Jm ε := by rw [hg', hJ]
  have hcont : Continuous (fun g : Mx k r => P * g * P⁻¹) := by fun_prop
  have := hc.comp hcont.continuousOn hmaps
  refine this.congr ?_
  intro g _
  show σ g v = σ (P⁻¹ * (P * g * P⁻¹) * P) v
  congr 2
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hdet, Matrix.one_mul,
    Matrix.mul_assoc, Matrix.nonsing_inv_mul P hdet, Matrix.mul_one]

end Formalism.FourierDecayAlt.P.S3dx4
