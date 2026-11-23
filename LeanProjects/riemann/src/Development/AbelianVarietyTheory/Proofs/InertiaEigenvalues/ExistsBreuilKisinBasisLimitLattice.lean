import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfClosedMembershipLimitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralElementsUnitFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitWittTiltAndNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinOEStabilityPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatPowDvdPerPowMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleBasisLimitLatticeTowerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LimitBreuilKisinBasisInvariantEtaleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantMapBreuilKisinMatrixStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MittagLefflerImageBreuilKisinModPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPreframeBoundedPolesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentCoefficientsAinfModPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfPrincipalIdealSaturatedClosedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBasisOfEtaleInvariantBoundedPolesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescendRightInverseStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ApproximatingLatticesTransitionMatrixModPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeApproximationMittagLefflerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LimitVectorMemOEAndAinfStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LimitVectorsInvertibleBasisOverOEStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SaturatedAinfLatticeFreeOverBreuilKisinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedMatrixCongruenceLiftSequenceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfExistsMulEqPowSmulOfModLPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfRightInverseUpToPowModLPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantEtaleBasisChangeByOEUnitStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

theorem limit_pre_exists : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val), ∃ (P : Pre bk N d fun g => (ρ g).val) (r : ℕ), ∀ n, ∃ m, n ≤ m ∧ Link bk P.T (F m).T (tw.Pi m) n r := by
  intro l _ K bk τ hτ d N ρ tw F
  obtain ⟨T0, hT0, hT0R⟩ := GlobalTheory.T.exists_etale_basis_limit_lattice_tower l K bk τ hτ d N ρ tw F
  obtain ⟨hfix0, A0, A0', hA0, hA0', hφ0, hAA0⟩ := GlobalTheory.T.limit_breuilKisin_basis_invariant_etale l K bk τ hτ d N ρ tw F T0 hT0 hT0R
  choose R R' hRO hR'O hR hRR' using hT0R
  obtain ⟨Yt, hYt⟩ := GlobalTheory.T.approximatingLattices_transitionMatrix_modPow l K bk τ hτ d N ρ tw F T0 R hT0 hR
  have hc := GlobalTheory.T.latticeApproximation_mittagLeffler l K bk τ hτ d N ρ tw F T0 R hT0 hRO hR
  have hlim := GlobalTheory.T.mittagLeffler_image_breuilKisin_modPow l K bk d tw.d' R Yt hYt hc
  have hL3 := GlobalTheory.T.limitVector_mem_OE_and_ainf l K bk τ hτ d N ρ tw F T0 R hRO hR
  obtain ⟨V, V', hVO, hV'O, hVV, hVlim⟩ := GlobalTheory.T.limitVectors_invertible_basis_over_OE l K bk d tw.d' R (fun n => ⟨R' n, hR'O n, hRR' n⟩) hlim hRO
  choose y1 hy1 using fun j => (hL3 _ (hVlim j)).2
  have hY1 : (Matrix.of fun i j => y1 j i).map (inclW l) = inclW l τ ^ N • (T0 * V) := by
    refine Matrix.ext fun i j => ?_
    have := congrFun (hy1 j) i
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
  obtain ⟨Y, Wm, Wm', hYu, hWO, hW'O, hWW, hYW, hmem⟩ := GlobalTheory.T.saturatedAinfLattice_free_over_breuilKisin l K bk τ hτ d N T0 V V' _ hT0 hVO hV'O hVV hY1
  have hlink := GlobalTheory.T.twisted_matrix_congruence_lift_sequence l K bk τ hτ d N ρ tw F T0 R hR hlim hL3 Y (T0 * Wm) hYW hmem
  obtain ⟨Y', hYY'⟩ := GlobalTheory.T.ainf_exists_mul_eq_pow_smul_of_mod_lPow l d (2 * N) τ Y hYu (fun n => by
    obtain ⟨m, _, Rn, Q, _, h⟩ := hlink n
    exact ⟨Rn.map bk.ev * Q, h⟩)
  obtain ⟨hfixT, A1, A1', hA1, hA1', hφ1, hAA1⟩ := GlobalTheory.T.invariantEtaleBasis_change_by_OE_unit l K bk d (fun g => (ρ g).val) T0 Wm Wm' A0 A0' hfix0 hA0 hA0' hφ0 hAA0 hWO hW'O hWW
  have hTu : IsUnit (T0 * Wm) := hT0.mul ⟨⟨Wm, Wm', hWW, mul_eq_one_comm.1 hWW⟩, rfl⟩
  obtain ⟨P, hP⟩ := GlobalTheory.T.breuilKisin_basis_of_etale_invariant_bounded_poles l K bk τ hτ N d (fun g => (ρ g).val) (T0 * Wm) A1 A1' Y Y' hTu hA1 hA1' hφ1 hAA1 hfixT hYW hYY'
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_right_inverse_mod_pow_of_ev l K bk τ hτ (2 * N)
  refine ⟨P, r, fun n => ?_⟩
  obtain ⟨m, hnm, Rn, Q, h1, h2⟩ := hlink n
  have h3 := GlobalTheory.T.ainf_rightInverse_up_to_pow_mod_lPow l d (tw.d' m) n (2 * N) τ Y Y' (Rn.map bk.ev) Q (GlobalTheory.T.breuilKisin_period_isUnit_wittTilt_and_ne_zero l K bk τ hτ).1 hYu hYY' h2
  obtain ⟨G, hG⟩ := hr d (tw.d' m) n Rn (Q * Y) h3
  exact ⟨m, hnm, Rn, G, by rw [hP]; exact h1, hG⟩

end GlobalTheory.BKLim
