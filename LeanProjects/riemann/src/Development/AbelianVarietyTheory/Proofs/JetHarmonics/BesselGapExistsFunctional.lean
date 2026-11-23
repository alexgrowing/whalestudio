import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapDimensionFormulaStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapNormIdentityStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapVanishingStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PositiveRankOneProportionalStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapExistsNonzeroStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsKTypeNonzeroBessel
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HaarEqSmul

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem exists_normalised_bessel_map : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∃ l, IsBeL R z π μW μN l := by
  intro H k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hDS hgap hok hside
  have hconv := GlobalTheory.T.besselIntegral_integrable_and_cwContinuous_of_gap H k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hside
  by_cases hz : ∃ w ∈ R.sm, ∃ v ∈ R.TK, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ≠ 0
  · obtain ⟨l₀, La, hB, hnz, hshape⟩ :=
      GlobalTheory.T.bessel_gap_exists_nonzero H k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hside hz
    have hTK : ∀ v ∈ R.TK, v ∈ R.sm :=
      (GlobalTheory.rep_basic_of_isDS H.1.2.2.1 k r ε mu R hDS).2.2.2.2.1
    obtain ⟨v₀, hv₀, hl₀⟩ := GlobalTheory.bessel_nonzero_on_translates H k r ε mu R Wp z π l₀ hDS hB hnz
    obtain ⟨c₀, -, hc₀⟩ := GlobalTheory.BesselDegree.schur_fdeg H k r ε μG hside.2.2.2.2.2.2.1
    have hP := GlobalTheory.T.bessel_integral_l2_norm_eq_div_formal_degree H k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hside _ (hc₀ mu R hDS).1
    have hadj := GlobalTheory.T.adjoint_besselIntegral_eq_swap_of_gap H k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hside
    obtain ⟨c, hc, hLa⟩ := GlobalTheory.T.positive_rank_one_proportional R.TK Wp (fun v => l₀ v) (fun v => La v)
      (fun v w => by
        have := hadj v v.2 w w.2
        rwa [hshape w (hTK _ w.2) v v.2, hshape v (hTK _ v.2) w w.2] at this)
      (fun v ξ => by
        have := hP v v.2 ξ
        rw [hshape v (hTK _ v.2) v v.2] at this
        exact ⟨this.1, this.2.1⟩)
      ⟨⟨v₀, hv₀⟩, hl₀⟩
    refine ⟨fun w => ((Real.sqrt c : ℝ) : ℂ) • l₀ w, Formalism.FourierDecayAlt.P.DDSmoothness.bessel_smul hB _, ?_⟩
    intro w hw v hv
    refine ⟨(hconv v hv).1 w hw, ?_⟩
    have hv' : La v = (c : ℂ) • l₀ v := hLa ⟨v, hv⟩
    rw [hshape w hw v hv, hv']
    ext ξ
    have hs : ((Real.sqrt c : ℝ) : ℂ) * ((Real.sqrt c : ℝ) : ℂ) = (c : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc]
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_left, Complex.conj_ofReal,
      smul_smul]
    congr 1
    rw [← hs]; ring
  · push Not at hz
    refine ⟨fun _ => 0, Formalism.FourierDecayAlt.P.DDSmoothness.bessel_zero, ?_⟩
    intro w hw v hv
    refine ⟨(hconv v hv).1 w hw, ?_⟩
    rw [hz w hw v hv]
    ext ξ
    simp

end GlobalTheory
