import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StronglyMeasurableTwistedLatticeSumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCharacterBilinearLawsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralEqFundamentalDomainLatticeSumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialCoefficientHeisenbergExpansionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShAdd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzLatticeSumBoundedAltBis

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem fold_abs {X ι : Type} [MeasurableSpace X] [Countable ι] (μ : Measure X) [SFinite μ] (S : Set X) (hS : μ S = 1)
    (Z T : X × X → ℂ) (hZ : StronglyMeasurable Z) (hT : StronglyMeasurable T) (B B₂ : ℝ)
    (hB : ∀ v, ‖Z v‖ ≤ B) (hB₂ : ∀ v, ‖T v‖ ≤ B₂)
    (c a : ι → X → ℂ) (hc : ∀ i, StronglyMeasurable (c i)) (hc1 : ∀ i x, ‖c i x‖ = 1)
    (ha : ∀ y, Summable fun i => ‖a i y‖) (hTs : ∀ y x, T (y, x) = ∑' i, c i x * a i y) :
    ∫ y in S, ∑' i, (∫ x in S, c i x * Z (y, x) ∂μ) * a i y ∂μ = ∫ v in S ×ˢ S, Z v * T v ∂(μ.prod μ) := by
  haveI : IsFiniteMeasure (μ.restrict S) := ⟨by simp [hS]⟩
  have hZs : ∀ y, StronglyMeasurable fun x => Z (y, x) := fun y => hZ.comp_measurable measurable_prodMk_left
  have inner : ∀ y, ∑' i, (∫ x in S, c i x * Z (y, x) ∂μ) * a i y = ∫ x in S, Z (y, x) * T (y, x) ∂μ := by
    intro y
    have hint : ∀ i, Integrable (fun x => c i x * Z (y, x) * a i y) (μ.restrict S) := by
      intro i
      refine Integrable.of_bound ((((hc i).mul (hZs y)).mul stronglyMeasurable_const).aestronglyMeasurable)
        (B * ‖a i y‖) (ae_of_all _ fun x => ?_)
      rw [norm_mul, norm_mul, hc1, one_mul]
      exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
    have hsum : Summable fun i => ∫ x in S, ‖c i x * Z (y, x) * a i y‖ ∂μ := by
      have h : ∀ i, ∫ x in S, ‖c i x * Z (y, x) * a i y‖ ∂μ = (∫ x in S, ‖Z (y, x)‖ ∂μ) * ‖a i y‖ := by
        intro i
        simp only [norm_mul, hc1, one_mul]
        exact integral_mul_const _ _
      simp only [h]
      exact (ha y).mul_left _
    have h1 := integral_tsum_of_summable_integral_norm hint hsum
    calc ∑' i, (∫ x in S, c i x * Z (y, x) ∂μ) * a i y
        = ∑' i, ∫ x in S, c i x * Z (y, x) * a i y ∂μ :=
          tsum_congr fun i => (integral_mul_const _ _).symm
      _ = ∫ x in S, ∑' i, c i x * Z (y, x) * a i y ∂μ := h1
      _ = ∫ x in S, Z (y, x) * T (y, x) ∂μ := by
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          show ∑' i, c i x * Z (y, x) * a i y = Z (y, x) * T (y, x)
          rw [hTs, ← tsum_mul_left]
          exact tsum_congr fun i => by ring
  simp only [inner]
  haveI hfin : IsFiniteMeasure ((μ.prod μ).restrict (S ×ˢ S)) := by
    rw [← Measure.prod_restrict]; infer_instance
  have hi : IntegrableOn (fun v => Z v * T v) (S ×ˢ S) (μ.prod μ) := by
    refine Integrable.of_bound ((hZ.mul hT).aestronglyMeasurable) (B * B₂) (ae_of_all _ fun v => ?_)
    rw [norm_mul]
    exact mul_le_mul (hB v) (hB₂ v) (norm_nonneg _) ((norm_nonneg _).trans (hB v))
  exact (setIntegral_prod (fun v => Z v * T v) hi).symm

theorem fj_fold_mean : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (F : G D n → ℂ), LeftInv (GF D n) F → ∀ (g : G D n) (θ : InfFam D), IsInfFam θ → ∀ φ ∈ schwartzA θ ρ p, ∀ B : ℝ, (∀ y x, ‖zc M m ψ b₀ F (M.nzx 0 x * (M.sh y * g))‖ ≤ B) → StronglyMeasurable (fun v : Mx D ρ p × Mx D ρ p => zc M m ψ b₀ F (M.nzx 0 v.2 * (M.sh v.1 * g))) → FJ M m ψ b₀ F g φ = ∫ v in m.𝓕 ×ˢ m.𝓕, zc M m ψ b₀ F (M.nzx 0 v.2 * (M.sh v.1 * g)) * conj (th ψ b₀ φ 0 v.2 v.1) ∂(m.μ.prod m.μ) := by
  intro D n ρ p hn M m ψ hψ b₀ F hF g θ hθ φ hφ B hB hZ
  obtain ⟨hH, hfd, h1⟩ := m.hμ
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D ρ p
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  haveI : SFinite m.μ := inferInstance
  haveI : IsFiniteMeasure (m.μ.restrict m.𝓕) := ⟨by simp [h1]⟩
  haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.toEquiv.injective.countable
  haveI : Countable (Matrix (Fin ρ) (Fin p) D.host.E) :=
    inferInstanceAs (Countable (Fin ρ → Fin p → D.host.E))
  obtain ⟨-, -, hnorm, -, -, hcont⟩ := GlobalTheory.T.heisenberg_character_bilinear_laws (ρ := ρ) (p := p) ψ hψ b₀
  have hφc : Continuous φ := GlobalTheory.RegSch.CentreWeilComm.continuous_of_mem hθ ⟨φ, hφ⟩
  have hφi : Integrable φ m.μ := GlobalTheory.RegSch.CentreWeilComm.integrable_of_mem hθ m.μ ⟨φ, hφ⟩
  obtain ⟨B₂, hB₂⟩ := GlobalTheory.T.exists_bound_lattice_sum_norm_schwartzA θ hθ φ hφ
  have hD := GlobalTheory.T.stronglyMeasurable_twisted_lattice_sum ψ hψ b₀ φ hφc.stronglyMeasurable (fun y => (hB₂ y).1)
  set Z : Mx D ρ p × Mx D ρ p → ℂ := fun v => zc M m ψ b₀ F (M.nzx 0 v.2 * (M.sh v.1 * g)) with hZdef
  have hpcm : StronglyMeasurable fun y => pc M m ψ b₀ F (M.sh y * g) :=
    hZ.integral_prod_right' (ν := m.μ.restrict m.𝓕)
  have hpcb : ∀ y, ‖pc M m ψ b₀ F (M.sh y * g)‖ ≤ B := by
    intro y
    have h := norm_integral_le_of_norm_le_const (μ := m.μ.restrict m.𝓕)
      (f := fun x => zc M m ψ b₀ F (M.nzx 0 x * (M.sh y * g))) (C := B) (ae_of_all _ fun x => hB y x)
    show ‖∫ x in m.𝓕, zc M m ψ b₀ F (M.nzx 0 x * (M.sh y * g)) ∂m.μ‖ ≤ B
    simpa [Measure.real, h1] using h
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hpcb 0)
  have hP : Integrable (fun y => pc M m ψ b₀ F (M.sh y * g) * conj (φ y)) m.μ := by
    refine (hφi.norm.const_mul B).mono'
      (hpcm.aestronglyMeasurable.mul (Complex.continuous_conj.comp hφc).aestronglyMeasurable) (ae_of_all _ fun y => ?_)
    rw [norm_mul, RCLike.norm_conj]
    exact mul_le_mul_of_nonneg_right (hpcb y) (norm_nonneg _)
  have hPξ : ∀ (y : Mx D ρ p) (ξ : Matrix (Fin ρ) (Fin p) D.host.E),
      pc M m ψ b₀ F (M.sh (rt ξ + y) * g) * conj (φ (rt ξ + y)) =
        (∫ x in m.𝓕, conj (chv ψ b₀ x (rt ξ)) * Z (y, x) ∂m.μ) * conj (φ (rt ξ + y)) := by
    intro y ξ
    rw [← GlobalTheory.CompanionTheory.FJE.sh_add M (rt ξ) y, mul_assoc, GlobalTheory.T.partial_coefficient_heisenberg_expansion M m ψ hψ b₀ F hF ξ (M.sh y * g)]
  have hfold := GlobalTheory.T.integral_eq_fundamental_domain_lattice_sum m _ hP
  have hmain := fold_abs m.μ m.𝓕 h1 Z (fun v => conj (dsum ψ b₀ φ v.2 v.1)) hZ
    (Complex.continuous_conj.comp_stronglyMeasurable hD) B B₂ (fun v => hB v.1 v.2)
    (fun v => ?_)
    (fun (ξ : Matrix (Fin ρ) (Fin p) D.host.E) x => conj (chv ψ b₀ x (rt ξ)))
    (fun (ξ : Matrix (Fin ρ) (Fin p) D.host.E) y => conj (φ (rt ξ + y)))
    (fun ξ => (Complex.continuous_conj.comp
      (hcont.comp (continuous_id.prodMk continuous_const))).stronglyMeasurable)
    (fun ξ x => by rw [RCLike.norm_conj]; exact hnorm _ _)
    (fun y => by simpa only [RCLike.norm_conj] using (hB₂ y).1)
    (fun y x => by
      show conj (dsum ψ b₀ φ x y) = _
      rw [dsum, Complex.conj_tsum]
      exact tsum_congr fun ξ => map_mul _ _ _)
  · show ∫ y, pc M m ψ b₀ F (M.sh y * g) * conj (φ y) ∂m.μ = _
    rw [hfold]
    simp only [hPξ]
    rw [hmain]
    simp only [th_zero]
    rfl
  · rw [RCLike.norm_conj, dsum]
    have hs : Summable fun ξ : Matrix (Fin ρ) (Fin p) D.host.E => ‖chv ψ b₀ v.2 (rt ξ) * φ (rt ξ + v.1)‖ := by
      simpa only [norm_mul, hnorm, one_mul] using (hB₂ v.1).1
    refine (norm_tsum_le_tsum_norm hs).trans ?_
    simpa only [norm_mul, hnorm, one_mul] using (hB₂ v.1).2

end GlobalTheory.CompanionTheory.FJE
