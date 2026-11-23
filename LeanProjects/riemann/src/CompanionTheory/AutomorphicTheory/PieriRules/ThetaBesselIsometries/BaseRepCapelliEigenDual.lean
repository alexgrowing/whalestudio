import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.ImportsBisTer
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselSettingGapDecayStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselSettingUniformConstantStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.CapelliKFiniteCoefficient
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselPeriodAdjointPairStatement
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.ExistsRegularRepBesselBigCellVectorEqBesselImpor
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.BesselNormSqEqBigCellNormSqAltImports
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.AemeasurableBesselNormIntegrandBigCellImports
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ExistsFamilyFunctionalsStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilyThroughDiscreteSeries
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.NumericalFamilyShapeGaps
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CoefZero

theorem continuousOn_of_ckOn {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞}
    {f : B.Mat k r → E} (h : B.CkOn m (B.GV k r) f) : ContinuousOn f (B.GV k r) := by
  letI : NormedAddCommGroup (B.Mat k r) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (B.Mat k r) := Matrix.normedSpace
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h g₀ hg₀
  have h1 : ContinuousWithinAt f' (B.GV k r) g₀ :=
    (hf'.continuousOn.continuousAt (hU.mem_nhds hgU)).continuousWithinAt
  refine h1.congr_of_eventuallyEq ?_ (he g₀ hgU hg₀)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hgU), self_mem_nhdsWithin] with g a b
  exact he g a b

theorem coef_norm_finite_and_zero : HypsG → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R0 : Rep P.k P.r) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), Num P.k P.r lam P.u b bv ga h q0 → R0.IsDG (PI.BesselPeriodGGP.eps48 P.k P.r) lam → PI.CapelliEig.IsKFinCoefT (k := P.k) (r := P.r) R0.σ f → TBB.jN2 p f < ⊤ ∧ (AEMeasurable fun c : Fin (P.r + 1) → ℂ => ENNReal.ofReal (TBB.Ew p (fun _ => 1) f (P.r + 1) [] (TBB.bigPt P.r c))) ∧ (TBB.jN2 p f = 0 → ∀ c : Fin (P.r + 1) → ℂ, D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) → p.V f (TBB.bigPt P.r c) = 0) := by
  intro hH P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R0 f hN hR0 hf
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  obtain ⟨R, hfam, hR⟩ := GlobalTheory.family_through_discreteSeries hH P.k P.r lam P.u b bv ga h q0 R0 hN hR0
  subst hR
  obtain ⟨l, l', dg, hl, hl'⟩ := GlobalTheory.T.exists_family_functionals hH P Wp Wq p lam b bv ga h q0 R hN hfam
  have h0 : n1 (0 : Fin (2 * P.r + P.k + 1) → ℤ) ≤ q0 := by simp [n1]
  obtain ⟨hB, hdg, hfd⟩ := hl 0 h0
  obtain ⟨hB', -, -⟩ := hl' 0 h0
  obtain ⟨⟨-, -, -, -, hok⟩, hν⟩ := GlobalTheory.NumFam.num_fam P.k P.r lam P.u b bv ga h q0 hN
  have hgap : Formalism.QuantumDeterminants.GapAtLeast (PI.BesselPeriodGGP.eps48 P.k P.r) lam (h / 2) := by
    simpa using (hν 0 h0).2.2.1
  obtain ⟨s, hs⟩ := (GlobalTheory.isCoef_of_translate_smul_exists hH.1.2.2.1 P.k P.r _ lam (R 0) Wp Wq (l 0) (l' 0) hR0).1 f hf
  obtain ⟨c, hc, hnorm⟩ := GlobalTheory.T.bessel_setting_uniform_constant hH P.k P.r Wp Wq p.T.base
  have hj : TBB.jN2 p f = ENNReal.ofReal (c * ‖s‖ ^ 2 / dg 0) := by
    rw [GlobalTheory.T.jN2_eq_normSq_base]
    exact hnorm _ lam (h / 2) (R 0) (l 0) (l' 0) (dg 0) hR0 hgap hok hB hB' hfd f s hs
  have hck := (GlobalTheory.T.smooth_and_inCC_of_isCoef_of_gap hH P.k P.r _ lam (h / 2) (R 0) Wp Wq (l 0) (l' 0) f s hR0 hgap hok hs).1
  refine ⟨by rw [hj]; exact ENNReal.ofReal_lt_top,
    GlobalTheory.T.aemeasurable_besselNormIntegrand_bigCell P Wp Wq p f (continuousOn_of_ckOn hck), fun hz x hx hG => ?_⟩
  have hs0 : s = 0 := by
    by_contra hne
    rw [hj, ENNReal.ofReal_eq_zero] at hz
    have hpos : 0 < ‖s‖ := norm_pos_iff.mpr hne
    have : 0 < c * ‖s‖ ^ 2 / dg 0 := by positivity
    linarith
  obtain ⟨γ, hγ, -, hV⟩ := GlobalTheory.T.exists_regularRep_besselBigCellVector_eq_bessel P Wp Wq p x hx hG
  obtain ⟨OO, hOO⟩ := GlobalTheory.T.bessel_orbital_integral_integrable_and_eq_smul hH P.k P.r _ lam (h / 2) (R 0) Wp Wq p.T.base (l 0) (l' 0) hR0 hgap hok hB hB'
  rw [hV f, (hOO f s hs γ hγ).2, hs0, zero_smul]

end GlobalTheory.CoefZero
