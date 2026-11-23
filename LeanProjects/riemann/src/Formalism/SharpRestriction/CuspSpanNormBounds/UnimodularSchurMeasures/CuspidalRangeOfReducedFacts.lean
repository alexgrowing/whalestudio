import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CuspidalRangeOfReproUnipotent
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrkbLeOneAddSq
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrkpCoefCont

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

theorem cu_countGF (X : CData) : cu.CountGF X := by
  have h : Countable (rr_GF X.I) := inferInstance
  exact (Set.countable_coe_iff (s := X.I.GFset)).1 h

theorem cu_measMul (X : CData) (hH : X.μf.IsHaarMeasure) : cu.MeasMul X := by
  have : SecondCountableTopology X.I.Gf := rr_secondCountable X.I X.μf
  exact measurable_fst.mul measurable_snd

theorem cu_extInv (X : CData) (hd : RegData X) : cu.ExtInv X := by
  classical
  intro T _ _ Fv _
  obtain ⟨hH, hF, -⟩ := hd
  have : (X.I.muA X.μf).IsMulLeftInvariant := rr_muA_left X.I X.μf
  have hfd := rr_FD_of X.I X.μf X.fund hF
  refine ⟨fun z => if z ∈ rr_N (rr_GF X.I) X.fund then 0 else X.I.ext Fv z, fun γ hγ y => ?_, ?_⟩
  · by_cases hy : y ∈ rr_N (rr_GF X.I) X.fund
    · have h2 : γ * y ∈ rr_N (rr_GF X.I) X.fund := by
        by_contra hcon
        have := rr_N_smul (Γ := rr_GF X.I) (D := X.fund) ((rr_GF X.I).inv_mem hγ) hcon
        rw [inv_mul_cancel_left] at this
        exact this hy
      simp only [hy, h2, if_true]
    · have h2 : γ * y ∉ rr_N (rr_GF X.I) X.fund := rr_N_smul (Γ := rr_GF X.I) hγ hy
      simp only [hy, h2, if_false]
      show (Fv : X.I.GA → ℂ) (rr_rep X.I.GFset X.fund (γ * y)) = (Fv : X.I.GA → ℂ) (rr_rep X.I.GFset X.fund y)
      rw [show rr_rep X.I.GFset X.fund (γ * y) = rr_rep X.I.GFset X.fund y from rr_rep_smul hfd hγ hy]
  · have hN : cu_mu X (rr_N (rr_GF X.I) X.fund) = 0 := rr_N_null hfd
    filter_upwards [compl_mem_ae_iff.2 hN] with z hz
    have hz' : z ∉ rr_N (rr_GF X.I) X.fund := hz
    simp only [hz', if_false]

theorem cu_extMeas (X : CData) (hd : RegData X) : cu.ExtMeas X := by
  intro T _ _ Fv _
  obtain ⟨hH, hF, -⟩ := hd
  have : (X.I.muA X.μf).IsMulLeftInvariant := rr_muA_left X.I X.μf
  have hfd := rr_FD_of X.I X.μf X.fund hF
  obtain ⟨r, hrm, hr⟩ := rr_exists_meas_rep hfd
  have hN : cu_mu X (rr_N (rr_GF X.I) X.fund) = 0 := rr_N_null hfd
  refine (((Lp.stronglyMeasurable Fv).comp_measurable hrm).aestronglyMeasurable).congr ?_
  filter_upwards [compl_mem_ae_iff.2 hN] with z hz
  obtain ⟨γ, h1, h2, h3⟩ := hr z
  show (Fv : X.I.GA → ℂ) (r z) = (Fv : X.I.GA → ℂ) (rr_rep X.I.GFset X.fund z)
  rw [h2, show rr_rep X.I.GFset X.fund z = γ * z from rr_rep_eq hfd hz h1 h3]

theorem cu_reproAE (X : CData) (hd : RegData X) (hu : UnimodA X) (hφm : Measurable X.φ) : cu.ReproAE X := by
  intro T hT hP Fv hFv
  obtain ⟨hH, hF, hR⟩ := hd
  have : SecondCountableTopology X.I.Gf := rr_secondCountable X.I X.μf
  have hL : (X.I.muA X.μf).IsMulLeftInvariant := rr_muA_left X.I X.μf
  have : (X.I.muA X.μf).IsMulRightInvariant := hu
  have : SigmaFinite (X.I.muA X.μf) := rr_muA_sigmaFinite X.I X.μf
  have hfd := rr_FD_of X.I X.μf X.fund hF
  obtain ⟨r, hrm, hr⟩ := rr_exists_meas_rep hfd
  have hTF : T Fv = Fv := by
    obtain ⟨u, rfl⟩ := hFv
    have h2 : T * T = T := hP.isIdempotentElem
    exact congrArg (fun S : X.L2 →L[ℂ] X.L2 => S u) h2
  have h1 := rrkb_step1 hfd hφm hrm hr (rr_IsReg_of X.I X.μf X.fund X.R hR) T hT.1 hT.2 Fv
  rw [hTF] at h1
  have hZ : X.μ {x | ¬ (Fv : X.I.GA → ℂ) x = ∫ g, X.φ g * (Fv : X.I.GA → ℂ) (r (x * g)) ∂(X.I.muA X.μf)} = 0 :=
    ae_iff.1 h1
  have hN : cu_mu X (rr_N (rr_GF X.I) X.fund) = 0 := rr_N_null hfd
  filter_upwards [cu_rep_avoid X hL (cu_countGF X) hF _ hZ] with z hz
  have hz' : (Fv : X.I.GA → ℂ) (X.I.rep X.fund z) =
      ∫ g, X.φ g * (Fv : X.I.GA → ℂ) (r (X.I.rep X.fund z * g)) ∂(X.I.muA X.μf) := by
    by_contra hcon
    exact hz hcon
  show (Fv : X.I.GA → ℂ) (X.I.rep X.fund z) = _
  rw [hz']
  obtain ⟨γ, g1, g2, -⟩ := rr_rep_spec hfd z
  have hNz : cu_mu X ((fun g => z * g) ⁻¹' rr_N (rr_GF X.I) X.fund) = 0 := by
    rw [measure_preimage_mul]; exact hN
  refine integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.2 hNz] with g hg
  have hg' : z * g ∉ rr_N (rr_GF X.I) X.fund := hg
  have e1 : X.I.rep X.fund z = γ * z := g2
  obtain ⟨γ', k1, k2, k3⟩ := hr (X.I.rep X.fund z * g)
  have e2 : r (X.I.rep X.fund z * g) = rr_rep X.I.GFset X.fund (z * g) := by
    rw [k2, e1]
    have k3' : (γ' * γ) * (z * g) ∈ X.fund := by
      rw [e1] at k3
      simpa [mul_assoc] using k3
    rw [show rr_rep X.I.GFset X.fund (z * g) = (γ' * γ) * (z * g) from
      rr_rep_eq hfd hg' ((rr_GF X.I).mul_mem k1 g1) k3']
    simp only [mul_assoc]
  rw [e2, mul_comm]
  rfl

def cu.Core (X : CData) : Prop :=
  cu.UnipFine X ∧ cu.HaarGrowth X ∧ cu.SizeStep X ∧ X.KernelDiag ∧ UnimodA X

theorem cu_fine_of_core (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (h : cu.Core X) : cu.Fine X := by
  obtain ⟨sU, sH, sS, sK, sA⟩ := h
  have hd := RegData_of_HypB X hX
  exact ⟨sU, sH, sS, sK, cu_reproAE X hd sA (rrk_phi_meas X hX), cu_extInv X hd, cu_extMeas X hd, cu_measMul X hd.1,
    cu_countGF X⟩

def cu_StepsCore (n₀ : ℕ) (A C : ℝ) : Prop :=
  ∀ X : CData, X.HypB n₀ A → X.GapAboveThreeHalvesPower → X.GapAboveSquareRootThreshold C → cu.Core X

theorem cuspidal_range_of_reduced_facts (X : CData) (D : Formalism.BasicNotions.D7) (hdec : DiscreteSeriesDecayBound D) {n₀ : ℕ} {A C : ℝ} (hn₀ : 1 ≤ n₀)
    (hC : 46 ≤ C) (hX : X.HypB n₀ A) (h1 : X.GapAboveThreeHalvesPower) (h2 : X.GapAboveSquareRootThreshold C) (hE : X.LowProj) (hF : cu.FinStep X)
    (hS : cu.Core X) : X.CuspStep :=
  cuspidal_range_of_fine_facts X D hdec hn₀ hC hX h1 h2 hE hF (cu_fine_of_core X hX hS)

end Formalism.MainNotions.LeviCoordinates
