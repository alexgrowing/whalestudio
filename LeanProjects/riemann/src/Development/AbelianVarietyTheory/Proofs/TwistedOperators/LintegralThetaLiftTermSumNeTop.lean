import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankFacGen
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal

noncomputable section

namespace GlobalTheory.ThetaLiftBound

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_rat_height_le {D : D7} (W : HSp D) (h : GA D W) :
    ∃ γ ∈ GQ W, GlobalTheory.Grow.height W (γ * h) ≤ 2 * GlobalTheory.Grow.quotHeight W h := by
  have hq := GlobalTheory.Grow.one_le_quotHeight W h
  by_contra hne
  push_neg at hne
  have : 2 * GlobalTheory.Grow.quotHeight W h ≤ GlobalTheory.Grow.quotHeight W h :=
    (GlobalTheory.Grow.le_quotHeight_iff W).2 fun γ hγ => (hne γ hγ).le
  linarith

theorem bound_pow (c a b M q : ℝ) (A : ℕ) (ha : 1 ≤ a) (haM : a ≤ M) (hb : 1 ≤ b) (hbq : b ≤ 2 * q) :
    c * (a * b) ^ A ≤ max c 0 * (M * (2 * q)) ^ A := by
  have hX : a * b ≤ M * (2 * q) := mul_le_mul haM hbq (by linarith) (by linarith)
  have hXp : (a * b) ^ A ≤ (M * (2 * q)) ^ A := pow_le_pow_left₀ (mul_nonneg (by linarith) (by linarith)) hX A
  exact (mul_le_mul_of_nonneg_right (le_max_left c 0) (pow_nonneg (mul_nonneg (by linarith) (by linarith)) A)).trans
    (mul_le_mul_of_nonneg_left hXp (le_max_right c 0))

theorem bound_mul (c M q f C' : ℝ) (A : ℕ) (hM : 0 ≤ M) (hq : 0 ≤ q) (hf : 0 ≤ f) (hF : f * q ^ A ≤ C') :
    max c 0 * (M * (2 * q)) ^ A * f ≤ max c 0 * (2 * M) ^ A * max C' 0 := by
  have e : max c 0 * (M * (2 * q)) ^ A * f = max c 0 * (2 * M) ^ A * (f * q ^ A) := by
    rw [mul_pow, mul_pow, mul_pow]; ring
  rw [e]
  exact mul_le_mul_of_nonneg_left (hF.trans (le_max_left _ _))
    (mul_nonneg (le_max_right c 0) (pow_nonneg (by linarith) A))

theorem lintegral_ne_top : ∀ (D : D7) (V W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C → ∀ (κ : Measure (NI V C)) (𝓝 : Set (NI V C)), κ.IsHaarMeasure → IsFundamentalDomain (NIQ V C) 𝓝 κ → ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν → ∀ F : GA D W → ℂ, GlobalTheory.Grow.RapidDec W F → ∀ (Sg : GA D V × GA D W → ℝ≥0∞), (∀ n ∈ NI V C, n ∈ GQ V → ∀ a b, Sg (n * a, b) = Sg (a, b)) → (∀ γ ∈ GQ W, ∀ a b, Sg (a, γ * b) = Sg (a, b)) → ∀ (A : ℕ) (c : ℝ), (∀ a b, Sg (a, b) ≤ ENNReal.ofReal (c * (GlobalTheory.Grow.height V a * GlobalTheory.Grow.height W b) ^ A)) → ∀ g : GA D V, ∫⁻ n in 𝓝, ∫⁻ h in 𝓕, Sg ((n : GA D V) * g, h) * ‖F h‖ₑ ∂ν ∂κ ≠ ⊤ := by
  intro D V W r C hC κ 𝓝 hκ h𝓝 ν 𝓕 hν h𝓕 F hF Sg h1 h2 A c hc g
  obtain ⟨K, hK, hcov⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D V r C ⟨hC.2.1, hC.2.2⟩).2
  obtain ⟨M, hM⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact V
    (hK.image (f := fun k : NI V C => (k : GA D V) * g) (by fun_prop))
  obtain ⟨C', hC'⟩ := hF.2.2 A
  have hbound : ∀ n : NI V C, ∀ h, Sg ((n : GA D V) * g, h) * ‖F h‖ₑ ≤
      ENNReal.ofReal (max c 0 * (2 * M) ^ A * max C' 0) := by
    intro n h
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov n
    obtain ⟨γ', hγ', hh⟩ := exists_rat_height_le W h
    have e1 : Sg (((γ * k : NI V C) : GA D V) * g, h) = Sg ((k : GA D V) * g, γ' * h) := by
      rw [Subgroup.coe_mul, mul_assoc, h1 _ γ.2 (Subgroup.mem_subgroupOf.1 hγ), h2 _ hγ']
    rw [e1]
    have hkM : GlobalTheory.Grow.height V ((k : GA D V) * g) ≤ M := hM _ ⟨k, hk, rfl⟩
    have hV1 := GlobalTheory.Grow.one_le_height V ((k : GA D V) * g)
    have hW1 := GlobalTheory.Grow.one_le_height W (γ' * h)
    have hq1 := GlobalTheory.Grow.one_le_quotHeight W h
    have hc1 := bound_pow c _ _ M (GlobalTheory.Grow.quotHeight W h) A hV1 hkM hW1 hh
    have hb := bound_mul c M (GlobalTheory.Grow.quotHeight W h) ‖F h‖ C' A (by linarith) (by linarith) (norm_nonneg _) (hC' h)
    calc Sg ((k : GA D V) * g, γ' * h) * ‖F h‖ₑ
        ≤ ENNReal.ofReal (max c 0 * (M * (2 * GlobalTheory.Grow.quotHeight W h)) ^ A) * ENNReal.ofReal ‖F h‖ := by
          rw [ofReal_norm_eq_enorm]
          exact mul_le_mul' ((hc _ _).trans (ENNReal.ofReal_le_ofReal hc1)) le_rfl
      _ = ENNReal.ofReal (max c 0 * (M * (2 * GlobalTheory.Grow.quotHeight W h)) ^ A * ‖F h‖) :=
          (ENNReal.ofReal_mul (mul_nonneg (le_max_right c 0)
            (pow_nonneg (mul_nonneg (by linarith) (by linarith)) A))).symm
      _ ≤ ENNReal.ofReal (max c 0 * (2 * M) ^ A * max C' 0) := ENNReal.ofReal_le_ofReal hb
  have hν𝓕 := (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol W ν 𝓕 hν h𝓕).ne
  have hκ𝓝 := GlobalTheory.TowerCT.vol D V r C hC κ 𝓝 hκ h𝓝
  refine ne_top_of_le_ne_top ?_ (lintegral_mono fun n => lintegral_mono fun h => hbound n h)
  rw [setLIntegral_const, setLIntegral_const]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hν𝓕) hκ𝓝

end GlobalTheory.ThetaLiftBound

end
