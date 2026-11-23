import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpOrbOfAmpDD
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemma3
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingExistence

open MeasureTheory Matrix

noncomputable section

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.QuantumDeterminants

theorem bsetting_of (k r : ℕ) (hk : 1 ≤ k) (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z ∧ 0 < Tz k r z)
    (hz' : inWb k r z' ∧ 0 < Tz k r z') :
    ∃ D : Formalism.FourierDecayAlt.B.RealPlaceData k r ℂ ℂ, D.z = z ∧ D.z' = z' := by
  obtain ⟨D, h1, h2, -, -, -⟩ := Formalism.FourierDecayAlt.P.setting_with_prescribed_data_exists k r ℂ ℂ z z'
    (fun _ => ContinuousLinearMap.id ℂ ℂ) (fun _ => ContinuousLinearMap.id ℂ ℂ) hk hz.1 hz'.1 hz.2 hz'.2
    ⟨rfl, fun _ _ _ _ => rfl⟩ ⟨rfl, fun _ _ _ _ => rfl⟩ (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    continuousOn_const continuousOn_const
  exact ⟨D, h1, h2⟩

theorem haarR_bi (k r : ℕ) (hk : 1 ≤ k) (L : Formalism.MainNotions.S.LocBessel k r)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR : Measure (Mt k r))
    (hγ : γ ∈ UH (Hpk k r)) (hmono : Formalism.FourierDecayAlt.C2.IsMonomial (Formalism.QuantumDeterminants.Zhat k r L.z L.z' γ))
    (hμ : Formalism.MainNotions.S.IsHaarOn (Formalism.MainNotions.S.RStab k r γ) μR) : Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.FourierDecayAlt.C6.Rset γ) μR := by
  obtain ⟨w, d, hd, hZ⟩ := hmono
  obtain ⟨D, hDz, hDz'⟩ := bsetting_of k r hk L.z L.z' L.hz L.hz'
  have hγG : γ ∈ Formalism.FourierDecayAlt.B.GV k r := hγ
  have hunit : IsUnit γ.det := (Formalism.FourierDecayAlt.P.unitary_group_closed k r).unit γ hγG
  have hcl := Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR (k := k) (r := r) hunit
  have hν := Formalism.FourierDecayAlt.P.radial_measure_is_haar k r ℂ ℂ D γ w d hγG hd (by rw [hDz, hDz']; exact hZ)
  exact Formalism.MainNotions.BridgeLemma₃.hu_general hcl hν hμ

theorem rStabInv_of_k (k r : ℕ) (hk : 1 ≤ k) (L : Formalism.MainNotions.S.LocBessel k r)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR : Measure (Mt k r))
    (hγ : γ ∈ UH (Hpk k r)) (hmono : Formalism.FourierDecayAlt.C2.IsMonomial (Formalism.QuantumDeterminants.Zhat k r L.z L.z' γ))
    (hμ : Formalism.MainNotions.S.IsHaarOn (Formalism.MainNotions.S.RStab k r γ) μR) :
    μR.map (fun x => fun i j => (Matrix.of x)⁻¹ i j) = μR := by
  obtain ⟨w, d, hd, hZ⟩ := hmono
  obtain ⟨D, hDz, hDz'⟩ := bsetting_of k r hk L.z L.z' L.hz L.hz'
  have hγG : γ ∈ Formalism.FourierDecayAlt.B.GV k r := hγ
  have hunit : IsUnit γ.det := (Formalism.FourierDecayAlt.P.unitary_group_closed k r).unit γ hγG
  have hcl := Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR (k := k) (r := r) hunit
  have hν := Formalism.FourierDecayAlt.P.radial_measure_is_haar k r ℂ ℂ D γ w d hγG hd (by rw [hDz, hDz']; exact hZ)
  have hμ' : Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.FourierDecayAlt.C6.Rset γ) μR := Formalism.MainNotions.BridgeLemma₃.hu_general hcl hν hμ
  exact Formalism.FourierDecayAlt.P.haar_measure_inversion k r _ μR hcl hμ'

theorem right_stabilizer_invariance : Formalism.MainNotions.S.Pv.AmpDD.RStabInv := by
  intro k r L γ μR hk hγ _ _ hmono hμ
  exact rStabInv_of_k k r hk L γ μR hγ hmono hμ

end Formalism.MainNotions.S.Pv.AmpDDPf
