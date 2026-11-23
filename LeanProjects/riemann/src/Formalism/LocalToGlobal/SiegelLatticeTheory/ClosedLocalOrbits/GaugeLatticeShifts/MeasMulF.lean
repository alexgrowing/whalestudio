import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.UMatInvMul
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SigmaFiniteOfB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants

namespace Formalism.L2.SG.RealObj.EnergyConvJ

variable {k r : ℕ}

def mulF (p : Mt k r × Mt k r) : Mt k r := fun i j => (Matrix.of p.1 * Matrix.of p.2) i j

theorem meas_mulF : Measurable (mulF (k := k) (r := r)) :=
  Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.RI.meas_mulP

theorem muS_eq (μW μN : Measure (Mt k r)) : Formalism.MainNotions.S.muS μW μN = (μW.prod μN).map mulF := rfl

theorem muS_inv {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) {μW μN : Measure (Mt k r)}
    (hW : Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z) μW) (hN : Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) μN) :
    (Formalism.MainNotions.S.muS μW μN).map Formalism.FourierDecayAlt.B2.invM = Formalism.MainNotions.S.muS μW μN := by
  have sW := Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.RI.sigmaFinite_of_b hW
  have sN := Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.RI.sigmaFinite_of_b hN
  have hinvm : Measurable (Formalism.FourierDecayAlt.B2.invM : Mt k r → Mt k r) := Formalism.FourierDecayAlt.P.B2x2.invM_meas
  have hWi : μW.map Formalism.FourierDecayAlt.B2.invM = μW :=
    Formalism.FourierDecayAlt.P.haar_measure_inversion k r (UWset k r z) μW (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z) hW
  have hNi : μN.map Formalism.FourierDecayAlt.B2.invM = μN :=
    Formalism.FourierDecayAlt.P.haar_measure_inversion k r (Nset k r) μN (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) hN
  have hNc : ∀ h ∈ UWset k r z, μN.map (conjM h) = μN := Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k r z μN hz hT hN

  let g : Mt k r → Mt k r → Mt k r := fun h n => mulF (mulF (h, Formalism.FourierDecayAlt.B2.invM n), Formalism.FourierDecayAlt.B2.invM h)
  have hgm : Measurable (Function.uncurry g) :=
    meas_mulF.comp ((meas_mulF.comp (measurable_fst.prodMk (hinvm.comp measurable_snd))).prodMk
      (hinvm.comp measurable_fst))
  have hW0 : ∀ᵐ h ∂μW, Matrix.of h ∈ UWset k r z := by rw [ae_iff]; exact hW.conc
  have hg : ∀ᵐ h ∂μW, μN.map (g h) = μN := by
    filter_upwards [hW0] with h hh
    have e : g h = conjM (Matrix.of h) ∘ Formalism.FourierDecayAlt.B2.invM := rfl
    rw [e, ← Measure.map_map (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.RI.meas_conj _) hinvm, hNi, hNc _ hh]
  have hmp : MeasurePreserving (fun p : Mt k r × Mt k r => (Formalism.FourierDecayAlt.B2.invM p.1, g p.1 p.2))
      (μW.prod μN) (μW.prod μN) :=
    MeasurePreserving.skew_product (μb := μW) (μd := μN) ⟨hinvm, hWi⟩ hgm hg
  have hFm : Measurable (fun p : Mt k r × Mt k r => (Formalism.FourierDecayAlt.B2.invM p.1, g p.1 p.2)) :=
    (hinvm.comp measurable_fst).prodMk hgm
  have hae : (Formalism.FourierDecayAlt.B2.invM ∘ mulF) =ᵐ[μW.prod μN]
      (mulF ∘ fun p : Mt k r × Mt k r => (Formalism.FourierDecayAlt.B2.invM p.1, g p.1 p.2)) := by
    have h1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := by
      rw [ae_iff]
      have es : {p : Mt k r × Mt k r | ¬ Matrix.of p.1 ∈ UWset k r z} =
          {x : Mt k r | Matrix.of x ∉ UWset k r z} ×ˢ Set.univ := by
        ext p; simp
      rw [es, Measure.prod_prod]
      have : μW {x : Mt k r | Matrix.of x ∉ UWset k r z} = 0 := hW.conc
      rw [this, zero_mul]
    filter_upwards [h1] with p hp
    have hu : IsUnit (Matrix.of p.1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ).det :=
      Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.RI.det_unit_of_UH hp.1
    have hii : (Matrix.of p.1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)⁻¹ * Matrix.of p.1 = 1 :=
      Matrix.nonsing_inv_mul _ hu
    show ((Matrix.of p.1 * Matrix.of p.2 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)⁻¹ :
        Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) =
      (Matrix.of p.1)⁻¹ * (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹)
    rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hii, Matrix.one_mul]
  rw [muS_eq, Measure.map_map hinvm meas_mulF, Measure.map_congr hae, ← Measure.map_map meas_mulF hFm, hmp.map_eq]

end Formalism.L2.SG.RealObj.EnergyConvJ
