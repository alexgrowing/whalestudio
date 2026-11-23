import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.Jets.TauZero
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSettingUniformConstantStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliKFiniteCoefficientStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselNormSqEqBigCellNormSqStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFamilyFunctionalsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilyFunctionalCoefficientStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilyFunctionalSpanStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGapsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilyThroughDiscreteSeries
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem suppliedData_exists : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R0 : Rep P.k P.r) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), Num P.k P.r lam P.u b bv ga h q0 → R0.IsDS (PI.BesselPeriodGGP.eps48 P.k P.r) lam → PI.CapelliEig.IsKFinCoefT (k := P.k) (r := P.r) R0.σ f → TBB.jN2 p f ≠ 0 → ∃ (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ) (t : ℝ), 0 < t ∧ J 0 = (fun g => (t : ℂ) • f g) ∧ Sup p lam q0 R l l' dg s J tau := by
  intro hH P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R0 f hN hR0 hf hj
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  obtain ⟨R, hfam, hR⟩ := GlobalTheory.family_through_discreteSeries hH P.k P.r lam P.u b bv ga h q0 R0 hN hR0
  subst hR
  obtain ⟨l, l', dg, hl, hl'⟩ := GlobalTheory.T.exists_family_functionals hH P Wp Wq p lam b bv ga h q0 R hN hfam
  have hK : PI.KFinSmooth := hH.1.2.2.1
  obtain ⟨s₀, hs₀⟩ := (GlobalTheory.T.capelli_k_finite_coefficient hK P.k P.r _ lam (R 0) Wp Wq (l 0) (l' 0) hR0).1 f hf
  have h0 : n1 (0 : Fin (2 * P.r + P.k + 1) → ℤ) ≤ q0 := by simp [n1]
  obtain ⟨⟨-, -, -, -, hgap⟩, hnum⟩ := GlobalTheory.T.numericalFamily_shape_gaps P.k P.r lam P.u b bv ga h q0 hN
  have hg : Formalism.QuantumDeterminants.GapAtLeast (PI.BesselPeriodGGP.eps48 P.k P.r) lam (h / 2) := by
    simpa using (hnum 0 h0).2.2.1
  obtain ⟨c, -, hc⟩ := GlobalTheory.T.bessel_setting_uniform_constant hH P.k P.r Wp Wq p.T.base
  have hne : s₀ ≠ 0 := by
    intro hz
    apply hj
    rw [GlobalTheory.T.jN2_eq_normSq_base P Wp Wq p f,
      hc _ lam (h / 2) (R 0) (l 0) (l' 0) (dg 0) hR0 hg hgap (hl 0 h0).1 (hl' 0 h0).1 (hl 0 h0).2.2 f s₀ hs₀, hz]
    simp
  obtain ⟨s, J, t, ht, hJ, hnz, hcoef, hzero⟩ :=
    GlobalTheory.T.family_functional_coefficient hH P Wp Wq p lam b bv ga h q0 R l l' dg f s₀ hfam hl hl' hs₀ hne
  obtain ⟨tau, htau⟩ :=
    GlobalTheory.T.family_functional_span hH P Wp Wq p lam b bv ga h q0 R l l' dg s J hN hfam hl hl' hnz hcoef hzero
  exact ⟨R, l, l', dg, s, J, tau, t, ht, hJ, htau⟩

end GlobalTheory
