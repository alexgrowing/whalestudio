import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OneMeasureSizes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFullLevelMeasureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryVolumeFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullLevelSelfDualLatticeStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop

namespace GlobalTheory.MassLower

theorem mass_lower : Hypotheses2 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m) (P : LevelP Cl.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (Formalism.L2.Theta.GA D (Wc D i))) (𝓕 : Set (Formalism.L2.Theta.GA D (Wc D i))), Formalism.IndefR.Lev.IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i P) μ 𝓕 → ENNReal.ofReal (Real.exp (-(C * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (Real.log ((D.R.f : ℝ) * D.R.r + 3) + 1) + Real.log |(discr D.host.E : ℝ)|)))) ≤ μ 𝓕 := by
  intro hP
  obtain ⟨c1, hc1, hc1', hB⟩ := GlobalTheory.T.full_level_self_dual_lattice
  obtain ⟨c2, hc2, hc2', hS⟩ := GlobalTheory.T.special_unitary_volume_family hP.p6
  have hc : 0 < c1 * c2 := mul_pos hc1 hc2
  have hcle : c1 * c2 ≤ 1 := mul_le_one₀ hc1' hc2.le hc2'
  refine ⟨-Real.log (c1 * c2), neg_nonneg.2 (Real.log_nonpos hc.le hcle), ?_⟩
  intro D Tu Cl t0 hC i P μ 𝓕 hF
  obtain ⟨μ', hF', hle⟩ := GlobalTheory.T.exists_full_level_measure D Tu Cl t0 hC i P μ 𝓕 hF
  letI : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨G, Λ, Ψ, x, p0, J, s, h2, hU, hSD, hΨ, hx, hs, hf, hb⟩ := hB D Tu Cl t0 hC i μ' 𝓕 hF'
  letI : MeasurableSpace (GlobalTheory.SUVol.realSU Ψ G) := borel _
  haveI : BorelSpace (GlobalTheory.SUVol.realSU Ψ G) := ⟨rfl⟩
  have hsu := hS D.host.E D.R.r G Λ Ψ x p0 J s h2 hU hSD hΨ hx hs
  rw [hf] at hsu
  set N : ℕ := D.R.f * D.R.r ^ 2 with hN
  have hlogd : 0 ≤ Real.log |(discr D.host.E : ℝ)| := by
    apply Real.log_nonneg
    have h0 : (discr D.host.E : ℝ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero D.host.E
    have : (1 : ℝ) ≤ |(discr D.host.E : ℤ)| := by
      exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero D.host.E)
    simpa using this
  have hlog3 : 0 ≤ Real.log ((D.R.f : ℝ) * D.R.r + 3) := by
    apply Real.log_nonneg
    have : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by positivity
    linarith
  have hNr : ((N : ℕ) : ℝ) = (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 := by rw [hN]; push_cast; ring
  have hC0 : 0 ≤ -Real.log (c1 * c2) := neg_nonneg.2 (Real.log_nonpos hc.le hcle)
  have key : Real.exp (-(-Real.log (c1 * c2) * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (Real.log ((D.R.f : ℝ) * D.R.r + 3) + 1) + Real.log |(discr D.host.E : ℝ)|))) ≤ c1 ^ N * c2 ^ N := by
    have e : (c1 * c2) ^ N = Real.exp (N * Real.log (c1 * c2)) := by rw [Real.exp_nat_mul, Real.exp_log hc]
    rw [← mul_pow, e]
    apply Real.exp_le_exp.2
    rw [hNr]
    have hA : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (Real.log ((D.R.f : ℝ) * D.R.r + 3) + 1) + Real.log |(discr D.host.E : ℝ)| := by
      have : 0 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 := by positivity
      nlinarith
    have hl : Real.log (c1 * c2) ≤ 0 := Real.log_nonpos hc.le hcle
    have := mul_le_mul_of_nonpos_left hA hl
    linarith
  calc ENNReal.ofReal (Real.exp (-(-Real.log (c1 * c2) * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (Real.log ((D.R.f : ℝ) * D.R.r + 3) + 1) + Real.log |(discr D.host.E : ℝ)|))))
      ≤ ENNReal.ofReal (c1 ^ N * c2 ^ N) := ENNReal.ofReal_le_ofReal key
    _ = ENNReal.ofReal (c1 ^ N) * ENNReal.ofReal (c2 ^ N) := ENNReal.ofReal_mul (by positivity)
    _ ≤ ENNReal.ofReal (c1 ^ N) * ∑' j, MeasureTheory.covolume (GlobalTheory.SUVol.inReal Ψ G (GlobalTheory.SUVol.ratStab G (Λ : Set (Fin D.R.r → D.host.E)) (s j))) (GlobalTheory.SUVol.realSU Ψ G) (GlobalTheory.SUVol.riemHaar Ψ G x) := by
        gcongr
    _ ≤ μ' 𝓕 := hb
    _ ≤ μ 𝓕 := hle

end GlobalTheory.MassLower
