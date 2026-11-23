import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SummableOneDivAbsNormSq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalVolumeRankOneProduct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicSumNondegenerateFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyMeasurableSetPrimV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ISupMulISupMono
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatStabOfIntegral
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimOne

theorem abs_sub_one_le {P L : ℝ≥0∞} {r A : ℝ} (hr : 0 ≤ r) (hL : L < ⊤) (hPL : P ≤ L)
    (h : L ≤ P + ENNReal.ofReal (2 * r) * L) (hA : |L.toReal - 1| ≤ A) :
    |P.toReal - 1| ≤ |L.toReal - 1| + 2 * (1 + A) * r := by
  have hP : P < ⊤ := lt_of_le_of_lt hPL hL
  have h1 : P.toReal ≤ L.toReal := ENNReal.toReal_mono hL.ne hPL
  have h2 : L.toReal ≤ P.toReal + 2 * r * L.toReal := by
    have hfin : P + ENNReal.ofReal (2 * r) * L ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨hP.ne, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL.ne⟩
    have := ENNReal.toReal_mono hfin h
    rwa [ENNReal.toReal_add hP.ne (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL.ne),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  have h3 : L.toReal ≤ 1 + A := by
    have := (abs_le.1 hA).2
    linarith
  have h4 : 2 * r * L.toReal ≤ 2 * (1 + A) * r := by
    have : 2 * r * L.toReal ≤ 2 * r * (1 + A) := mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith
  have h5 : |P.toReal - L.toReal| ≤ 2 * (1 + A) * r := by
    rw [abs_le]
    constructor <;> linarith [mul_nonneg (by positivity : (0:ℝ) ≤ 2 * r) (ENNReal.toReal_nonneg (a := L))]
  calc |P.toReal - 1| = |(P.toReal - L.toReal) + (L.toReal - 1)| := by ring_nf
    _ ≤ |P.toReal - L.toReal| + |L.toReal - 1| := abs_add_le _ _
    _ ≤ |L.toReal - 1| + 2 * (1 + A) * r := by linarith

theorem prim_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (h₂ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b) (minf : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin (M + 2) → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E)), IsGramFibFree (Ainf F) σ (hypOne J) 1 (coordW (Ainf F) b laminf 1 (M + 2)) (coordHerm (Ainf F) σ b laminf 1) minf → (∀ v, IsGramFibFree (Fv F v) σ (hypOne J) 1 (coordW (Fv F v) b (lam v) 1 (M + 2)) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → ∀ I : Measure (Fin 1 → Fin (M + 2) → AF F ⊗[F] E), IsEulerProd b I 1 (minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂)) (fun v => m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂)) → Summable (fun v => |(m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (primV σ J b v)).toReal - 1|) ∧ ∃ S₃ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₃ ⊆ S → ∀ (Ψinf : (Fin 1 → Fin (M + 2) → Ainf F ⊗[F] E) → ℝ≥0∞) (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable Ψinf → (∀ v, Measurable (Ψ v)) → ∫⁻ y, purePr σ J b S Ψinf Ψ y ∂I = ((∫⁻ y, Ψinf y ∂(minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂))) * ∏ v ∈ S, ∫⁻ y, Ψ v y ∂(m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂))) * ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (primV σ J b v.1)).toReal) := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM d b laminf lam hinf hlam h₂ minf m hfinf hfv I hE
  have hND := (GlobalTheory.CompanionTheory.WeilSiegel.HypStep.hypOne_isHermND_and_e0_mem F E σ hCM M J hJ).1
  have hSF := GlobalTheory.CompanionTheory.WeilSiegel.FreeLocal.free_fibre_zero F E σ hCM (M + 2) (hypOne J) hND (by omega) h₂ d b laminf lam hinf hlam
    minf hfinf m hfv
  have hgood := (GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimLoc.prim_local F E σ hCM M J hJ (by omega) d b).and (GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimMeas.eventually_measurableSet_primV F E σ hCM M J hJ d b)
  obtain ⟨hfin, hsumL, -⟩ := id hE
  have hsum : Summable (fun v => |(m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂)
      (primV σ J b v)).toReal - 1|) := by
    set A : ℝ := ∑' v, |(m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂)
      (latV b v)).toReal - 1| with hAdef
    have hb := (hsumL.add (((GlobalTheory.CompanionTheory.SW.Primes.summable_one_div_absNorm_sq F).mul_left
      (2 * (1 + A)))))
    refine Summable.of_norm_bounded_eventually hb ?_
    filter_upwards [hgood] with v hv
    obtain ⟨⟨hsub, hmass⟩, -⟩ := hv
    have h := hmass (lam v) (hlam v) (m v) (hfv v) h₂
    have hle : |(m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (latV b v)).toReal - 1| ≤ A :=
      hsumL.le_tsum v (fun _ _ => abs_nonneg _)
    have hr : (0 : ℝ) ≤ 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2 := by positivity
    have h' := abs_sub_one_le hr (hfin v) (measure_mono hsub) (by
      have e : (2 : ℝ) * (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) = 2 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2 := by
        ring
      rw [e]
      exact h) hle
    rw [Real.norm_eq_abs, abs_abs]
    simpa [mul_assoc] using h'
  refine ⟨hsum, ?_⟩
  have hfinS : {v | ¬ ((primV σ J b v ⊆ latV b v) ∧ MeasurableSet (primV σ J b v))}.Finite := by
    have h : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
        (primV σ J b v ⊆ latV b v) ∧ MeasurableSet (primV σ J b v) := by
      filter_upwards [hgood] with v hv
      exact ⟨hv.1.1, hv.2⟩
    exact Filter.eventually_cofinite.1 h
  exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimFormula.prim_formula F E σ hCM M J hJ d b I _ _ hE hSF.1 hSF.2.1 hfinS.toFinset
    (fun v hv => by
      by_contra hc
      exact hv (hfinS.mem_toFinset.2 hc)) hsum

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimOne
