import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StronglyMeasurableTwistedLatticeSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCharacterBilinearLaws
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralEqFundamentalDomainLatticeSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCharacterOrthogonalityStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem fold_parseval : ∀ {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, b₀.1.det ≠ 0 → ∀ (Φ φ : Mx D ρ p → ℂ) (B₁ B₂ : ℝ), StronglyMeasurable Φ → StronglyMeasurable φ → (∀ y, Summable (fun ξ : Matrix (Fin ρ) (Fin p) D.host.E => ‖Φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖) ∧ ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖Φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖ ≤ B₁) → (∀ y, Summable (fun ξ : Matrix (Fin ρ) (Fin p) D.host.E => ‖φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖) ∧ ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖ ≤ B₂) → ∫ v in m.𝓕 ×ˢ m.𝓕, GlobalTheory.CompanionTheory.FJE.Ap ψ b₀ Φ φ v ∂(m.μ.prod m.μ) = ∫ y, Φ y * conj (φ y) ∂m.μ := by
  intro D ρ p m ψ hψ b₀ hb Φ φ B₁ B₂ hΦ hφ h1 h2
  haveI := m.hμ.1
  have hfd : IsAddFundamentalDomain (ratMx D ρ p) m.𝓕 m.μ := m.hμ.2.1
  have hfin : m.μ m.𝓕 = 1 := m.hμ.2.2
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin ρ) (Fin p) D.host.E) :=
    inferInstanceAs (Countable (Fin ρ → Fin p → D.host.E))
  haveI : Countable (ratMx D ρ p) := by
    unfold GlobalTheory.MixModel.ratMx
    exact (AddMonoidHom.rangeRestrict_surjective _).countable
  haveI : MeasurableConstVAdd (ratMx D ρ p) (Mx D ρ p) :=
    ⟨fun c => (continuous_const.add continuous_id).measurable⟩
  haveI : SFinite m.μ := by
    have hs := hfd.sum_restrict
    open scoped Pointwise in
    haveI : ∀ g : ratMx D ρ p, IsFiniteMeasure (m.μ.restrict (g +ᵥ m.𝓕)) := fun g =>
      ⟨by rw [Measure.restrict_apply_univ, measure_vadd, hfin]; exact ENNReal.one_lt_top⟩
    rw [← hs]
    infer_instance
  haveI : IsFiniteMeasure (m.μ.restrict m.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, hfin]; exact ENNReal.one_lt_top⟩
  have hds : ∀ (Ψ : Mx D ρ p → ℂ) (B : ℝ),
      (∀ y, Summable (fun ξ : Matrix (Fin ρ) (Fin p) D.host.E => ‖Ψ (rt ξ + y)‖) ∧
        ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖Ψ (rt ξ + y)‖ ≤ B) →
      ∀ x y, ‖dsum ψ b₀ Ψ x y‖ ≤ B := by
    intro Ψ B hB x y
    refine (norm_tsum_le_tsum_norm ?_).trans ?_
    · simpa [norm_mul, chv_norm ψ hψ] using (hB y).1
    · simpa [norm_mul, chv_norm ψ hψ] using (hB y).2
  have hB₁ : 0 ≤ B₁ := (tsum_nonneg (fun _ => norm_nonneg _)).trans (h1 0).2
  have hB₂ : 0 ≤ B₂ := (tsum_nonneg (fun _ => norm_nonneg _)).trans (h2 0).2
  have hm : StronglyMeasurable (Ap ψ b₀ Φ φ) :=
    (dsum_stronglyMeasurable ψ hψ b₀ Φ hΦ (fun y => (h1 y).1)).mul
      (Complex.continuous_conj.comp_stronglyMeasurable
        (dsum_stronglyMeasurable ψ hψ b₀ φ hφ (fun y => (h2 y).1)))
  have hint : Integrable (Ap ψ b₀ Φ φ) ((m.μ.restrict m.𝓕).prod (m.μ.restrict m.𝓕)) := by
    refine Integrable.of_bound hm.aestronglyMeasurable (B₁ * B₂) (ae_of_all _ (fun v => ?_))
    rw [Ap, norm_mul, Complex.norm_conj]
    exact mul_le_mul (hds Φ B₁ h1 _ _) (hds φ B₂ h2 _ _) (norm_nonneg _) hB₁
  have hP : StronglyMeasurable (fun y => Φ y * conj (φ y)) :=
    hΦ.mul (Complex.continuous_conj.comp_stronglyMeasurable hφ)
  have hsum : ∀ y, ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖Φ (rt ξ + y) * conj (φ (rt ξ + y))‖ₑ
      ≤ ENNReal.ofReal (B₁ * B₂) := by
    intro y
    calc ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖Φ (rt ξ + y) * conj (φ (rt ξ + y))‖ₑ
        ≤ ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E,
            ‖Φ (rt ξ + y)‖ₑ * ∑' η : Matrix (Fin ρ) (Fin p) D.host.E, ‖φ (rt η + y)‖ₑ := by
          refine ENNReal.tsum_le_tsum (fun ξ => ?_)
          rw [enorm_mul, ← ofReal_norm (conj _), Complex.norm_conj, ofReal_norm]
          gcongr
          exact ENNReal.le_tsum (f := fun η => ‖φ (rt η + y)‖ₑ) ξ
      _ = (∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖Φ (rt ξ + y)‖ₑ) *
            ∑' η : Matrix (Fin ρ) (Fin p) D.host.E, ‖φ (rt η + y)‖ₑ := ENNReal.tsum_mul_right
      _ ≤ ENNReal.ofReal B₁ * ENNReal.ofReal B₂ := by
          gcongr
          · simp only [← ofReal_norm]
            rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (h1 y).1]
            exact ENNReal.ofReal_le_ofReal (h1 y).2
          · simp only [← ofReal_norm]
            rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (h2 y).1]
            exact ENNReal.ofReal_le_ofReal (h2 y).2
      _ = ENNReal.ofReal (B₁ * B₂) := (ENNReal.ofReal_mul hB₁).symm
  have hPint : Integrable (fun y => Φ y * conj (φ y)) m.μ := by
    refine ⟨hP.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    rw [hfd.lintegral_eq_tsum'']
    beta_reduce
    rw [← lintegral_tsum (f := fun (g : ratMx D ρ p) (x : Mx D ρ p) => ‖Φ (g +ᵥ x) * conj (φ (g +ᵥ x))‖ₑ)
      (fun g => ((hP.measurable.comp (measurable_const_vadd g)).enorm).aemeasurable)]
    calc ∫⁻ x in m.𝓕, ∑' g : ratMx D ρ p, ‖Φ (g +ᵥ x) * conj (φ (g +ᵥ x))‖ₑ ∂m.μ
        ≤ ∫⁻ _ in m.𝓕, ENNReal.ofReal (B₁ * B₂) ∂m.μ := by
          refine lintegral_mono (fun x => ?_)
          refine (ENNReal.tsum_le_tsum_comp_of_surjective
            (AddMonoidHom.rangeRestrict_surjective
              (Formalism.L2.Theta.incA D).toAddMonoidHom.mapMatrix) _).trans ?_
          exact hsum x
      _ < ⊤ := by
          rw [lintegral_const, Measure.restrict_apply_univ, hfin, mul_one]
          exact ENNReal.ofReal_lt_top
  rw [← Measure.prod_restrict, integral_prod _ hint, integral_fold m _ hPint]
  refine integral_congr_ae (ae_of_all _ (fun y => ?_))
  exact GlobalTheory.T.heisenberg_character_orthogonality m ψ hψ b₀ hb (fun η => Φ (rt η + y)) (fun η => φ (rt η + y)) (h1 y).1 (h2 y).1

end GlobalTheory.CompanionTheory.FJE
