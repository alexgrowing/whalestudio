import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratPeriodMatrixExistsFixedFrobeniusSolutionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivariantPhiModuleMatrixMemOEStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfLiftPeriodPowSmulIntertwinerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerSeriesLiftOfPeriodPowSmulIntegralMatrStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrobeniusPeriodStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

theorem GlobalTheory.BSP.equivariant_matrix_over_bk : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l)) (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' → ∀ f : Matrix (Fin d') (Fin d) ℤ_[l], (∀ g, f * ρ g = ρ' g * f) → ∃ Y : Matrix (Fin d') (Fin d) bk.S, T' * Y.map bk.evW = zW f * T := by
  intro l _ K bk d d' S S' ρ ρ' T T' hT hT' f hf
  obtain ⟨X, hX, hfix, hphi⟩ := GlobalTheory.T.stratPeriodMatrix_exists_fixed_frobenius_solution l K bk d d' S S' ρ ρ' T T' hT hT' f hf
  have hOE := GlobalTheory.T.equivariant_phiModule_matrix_mem_OE l K bk d d' S S' X hfix hphi
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_breuilKisin_frobenius_period l K bk
  obtain ⟨M, x, hx⟩ := GlobalTheory.T.exists_ainf_lift_period_pow_smul_intertwiner l K bk τ hτ d d' S S' ρ ρ' T T' hT hT' f X hX
  obtain ⟨Y, hY⟩ := GlobalTheory.T.exists_powerSeries_lift_of_period_pow_smul_integral_matrix l K bk τ hτ d d' M X x hOE hx
  exact ⟨Y, by rw [hY]; exact hX⟩
