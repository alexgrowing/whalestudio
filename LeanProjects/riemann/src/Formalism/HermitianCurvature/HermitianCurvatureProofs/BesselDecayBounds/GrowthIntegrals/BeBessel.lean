import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.NonnegNormSums.SumNonnegNorms
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.IdempotentTranslateMeasurable
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvSig
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvPsi
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvPi
import Formalism.SharpRestriction.CuspSpanNormBounds.DoubleBoundAndExtensionOfSmooth

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.MainNotions.BeBesselW

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL PI.WBL.Cv PI.WBL.Cv.BeC

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]

theorem bessel_on (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN : Measure (Mt k r)) [SFinite μN] (σ : Mx k r → (H →L[ℂ] H)) {V : H → Prop}
    (hG : GrpF k r z) (hσ : SigU σ) (hπ : PiU z π) (hψ : PsiF k r z c) (hM : MeasF z π μW μN)
    (hD : DecayOn μW μN σ V) {v : H} (hv : V v) (ξ : Wp) :
    IsBesselMapSm z (psi k r z c) σ π (fun u => be z c π μW μN σ u v ξ) := by
  refine ⟨fun w hw w' hw' => ?_, fun a w hw => ?_, fun h hh m hm w hw => ?_,
    cont_on z c π μW μN σ hG hπ hM hD v hv ξ⟩
  · show be z c π μW μN σ (w + w') v ξ = be z c π μW μN σ w v ξ + be z c π μW μN σ w' v ξ
    have e : be z c π μW μN σ (w + w') v = be z c π μW μN σ w v + be z c π μW μN σ w' v := by
      unfold be
      rw [← integral_add (int_on z c π μW μN σ hG hπ hM hD w hw v hv)
        (int_on z c π μW μN σ hG hπ hM hD w' hw' v hv)]
      congr 1
      funext p
      unfold beF
      rw [map_add, inner_add_right, add_mul, add_smul]
    rw [e]
    rfl
  · show be z c π μW μN σ (a • w) v ξ = a • be z c π μW μN σ w v ξ
    have e : be z c π μW μN σ (a • w) v = a • be z c π μW μN σ w v := by
      unfold be
      rw [← integral_smul]
      congr 1
      funext p
      unfold beF
      rw [map_smul, inner_smul_right, mul_assoc, mul_smul]
    rw [e]
    rfl
  · show be z c π μW μN σ (σ (h * m) w) v ξ = psi k r z c m • π h (be z c π μW μN σ w v ξ)
    rw [equiv_on z c π μW μN σ hG hσ hπ hψ hM hD h hh m hm w hw v hv]
    rfl

theorem bessel_on_FI (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN : Measure (Mt k r)) [SFinite μN] (σ : Mx k r → (H →L[ℂ] H)) {V : H → Prop}
    (hG : GrpF k r z) (hσ : SigU σ) (hπ : PiU z π) (hψ : PsiF k r z c) (hM : MeasF z π μW μN)
    (hD : DecayOn μW μN σ V) {v : H} (hv : V v) (ξ : Wp) :
    IsBesselMapSm z (psi k r z c) σ π
      (fun u => (∫ p, Formalism.MainNotions.DoubleDerivativeSmoothness.FI z c π σ u v p ∂(μW.prod μN)) ξ) :=
  bessel_on z c π μW μN σ hG hσ hπ hψ hM hD hv ξ

theorem beBessel_DD {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {u : Fin k → ℝ}
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN : Measure (Mt k r)) [SFinite μN] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H) (a : ℝ)
    (hσ : IsDSHpk k r ε lam σ) (hz : inWb k r z) (hT : 0 < Tz k r z) (hπ : IsHCTypeW k r z u π)
    (hM : MeasF z π μW μN)
    (hgr : Integrable (fun p : Mt k r × Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2 : Mx k r) ^ (1 - a))
      (μW.prod μN))
    (ha : 1 ≤ a) (h0 : PtB σ a w0) :
    ∀ v ∈ Formalism.MainNotions.BridgeLemma₄.DDsp σ w0, ∀ ξ : Wp, IsBesselMapSm z (psi k r z c) σ π
      (fun u => (∫ p, Formalism.MainNotions.DoubleDerivativeSmoothness.FI z c π σ u v p ∂(μW.prod μN)) ξ) := by
  intro v hv ξ
  have hG := grpAll k r z
  have hS := sigAll k r ε lam H σ hσ
  have hP := piAll k r z u Wp π hz hT hπ
  have hψ := psiAll k r z c hz
  have hD : DecayOn μW μN σ (fun v => v ∈ Formalism.MainNotions.BridgeLemma₄.DDsp σ w0) :=
    decayOn_of_pt z π μW μN σ a hG hM (fun w => Formalism.MainNotions.LeviCoordinates.discrete_series_continuousOn hσ w) hgr (ptDec_DD hG hS ha h0)
  exact bessel_on_FI z c π μW μN σ hG hS hP hψ hM hD hv ξ

theorem beBessel_K {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {u : Fin k → ℝ}
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN : Measure (Mt k r)) [SFinite μN] (σ : Mx k r → (H →L[ℂ] H)) (a : ℝ)
    (hσ : IsDSHpk k r ε lam σ) (hz : inWb k r z) (hT : 0 < Tz k r z) (hπ : IsHCTypeW k r z u π)
    (hM : MeasF z π μW μN)
    (hgr : Integrable (fun p : Mt k r × Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2 : Mx k r) ^ (1 - a))
      (μW.prod μN))
    (hK : PtDec σ a (fun v => IsKFinHpk (k := k) (r := r) σ v)) :
    ∀ v : H, IsKFinHpk (k := k) (r := r) σ v → ∀ ξ : Wp, IsBesselMapSm z (psi k r z c) σ π
      (fun u => (∫ p, Formalism.MainNotions.DoubleDerivativeSmoothness.FI z c π σ u v p ∂(μW.prod μN)) ξ) := by
  intro v hv ξ
  have hG := grpAll k r z
  have hS := sigAll k r ε lam H σ hσ
  have hP := piAll k r z u Wp π hz hT hπ
  have hψ := psiAll k r z c hz
  have hD : DecayOn μW μN σ (fun v => IsKFinHpk (k := k) (r := r) σ v) :=
    decayOn_of_pt z π μW μN σ a hG hM (fun w => Formalism.MainNotions.LeviCoordinates.discrete_series_continuousOn hσ w) hgr hK
  exact bessel_on_FI z c π μW μN σ hG hS hP hψ hM hD hv ξ

end Formalism.MainNotions.BeBesselW
