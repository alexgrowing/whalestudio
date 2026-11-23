import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilFormulaRange
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteProductRenormalizationStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureIntegralStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeStableAlmostEverywhereStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjectionsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyRealStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaMeasureLocallyFiniteInvariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalVolumeRankOneIsotropicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalVolumeRankOneProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteVolumeRankOneProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalVolumeRankOneNormalisedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteVolumeRankOneEulerStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.OneZero

theorem one_vector_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E)).Nonempty → SWFree σ J (0 : Matrix (Fin 1) (Fin 1) E) h₀ := by
  intro F E _ _ _ _ _ σ hcm M J hJ hM h₀ hne d b li lam hli hlam μ 𝓕 hμ h𝓕 mi m hmi hm
  classical
  obtain ⟨t0, t1, t2⟩ := GlobalTheory.T.theta_measure_locally_finite_invariant F E σ hcm M J hJ hM μ 𝓕 hμ h𝓕
  set I := thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E)) with hI
  set m0 : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin M → Fv F v ⊗[F] E) :=
    fun v => m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) with hm0
  set mi0 := mi (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) with hmi0
  obtain ⟨sfi, sfv, hnz⟩ := GlobalTheory.T.global_volume_rank_one_product F E σ hcm M J hJ hM h₀ d b li lam hli hlam mi hmi m hm
  obtain ⟨nzi, nzv⟩ := hnz hne
  obtain ⟨hfin, hsum⟩ := GlobalTheory.T.finite_volume_rank_one_product F E σ hcm M J hJ hM h₀ d b lam hlam m hm
  choose cS hcS using GlobalTheory.T.global_volume_rank_one_isotropic F E σ hcm M J hJ hM h₀ d b li lam hli hlam mi hmi m hm I t0 t1 t2
  obtain ⟨A, hAm, hA0, hAt⟩ := @GlobalTheory.CompanionTheory.SW.Fact.exists_test_set _ _ mi0 sfi nzi
  choose B hBm hB0 hBt using fun v => @GlobalTheory.CompanionTheory.SW.Fact.exists_test_set _ _ (m0 v) (sfv v) (nzv v)
  have hLv : ∀ v, IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F
  have hstep : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∅ ⊆ S → ∀ v, v ∉ S →
      (cS S : ℝ) = cS (insert v S) * (m0 v (latV b v)).toReal := by
    intro S _ v hv
    have hlatm : MeasurableSet (latV b v : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) := by
      haveI := GlobalTheory.CompanionTheory.SW.Fact.borel_tup σ hcm (Fv F v) (hLv v) 1 M
      exact ((GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 M).2.2.2.1 v).2.measurableSet
    let φ0 : ∀ w : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin M → Fv F w ⊗[F] E) → ℝ≥0∞ :=
      fun w => (B w).indicator 1
    let φ1 := Function.update φ0 v ((latV b v).indicator 1)
    have hφ0 : ∀ w, Measurable (φ0 w) := fun w => measurable_one.indicator (hBm w)
    have hφ1 : ∀ w, Measurable (φ1 w) := by
      intro w
      by_cases hw : w = v
      · subst hw
        simpa [φ1] using measurable_one.indicator hlatm
      · simpa [φ1, Function.update_of_ne hw] using hφ0 w
    have hAφ : Measurable (A.indicator (1 : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)) := measurable_one.indicator hAm
    have e1 : ∫⁻ X, pureL b S (A.indicator 1) φ0 X ∂I = (cS S : ℝ≥0∞) * ((∫⁻ X, A.indicator (1 : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) X ∂mi0) * ∏ w ∈ S, ∫⁻ X, φ0 w X ∂(m0 w)) :=
      hcS S _ φ0 hAφ hφ0
    have e2 : ∫⁻ X, pureL b (insert v S) (A.indicator 1) φ1 X ∂I = (cS (insert v S) : ℝ≥0∞) * ((∫⁻ X, A.indicator (1 : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) X ∂mi0) * ∏ w ∈ insert v S, ∫⁻ X, φ1 w X ∂(m0 w)) :=
      hcS (insert v S) _ φ1 hAφ hφ1
    have e3 : ∫⁻ X, pureL b (insert v S) (A.indicator 1) φ1 X ∂I =
        ∫⁻ X, pureL b S (A.indicator 1) φ0 X ∂I :=
      lintegral_congr fun X => GlobalTheory.CompanionTheory.SW.Fact.pureL_insert b S v hv _ φ0 X
    rw [e3, e1, Finset.prod_insert hv] at e2
    have hp : ∏ w ∈ S, ∫⁻ X, φ1 w X ∂(m0 w) = ∏ w ∈ S, ∫⁻ X, φ0 w X ∂(m0 w) :=
      Finset.prod_congr rfl fun w hw => by
        have hne : w ≠ v := fun h => hv (h ▸ hw)
        simp only [φ1, Function.update_of_ne hne]
    have hL : ∫⁻ X, φ1 v X ∂(m0 v) = m0 v (latV b v) := by
      simp only [φ1, Function.update_self]
      exact lintegral_indicator_one hlatm
    have hB : ∀ w, ∫⁻ X, φ0 w X ∂(m0 w) = m0 w (B w) := fun w => lintegral_indicator_one (hBm w)
    have hA : ∫⁻ X, A.indicator (1 : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) X ∂mi0 = mi0 A :=
      lintegral_indicator_one hAm
    rw [hp, hL, hA] at e2
    simp only [hB] at e2
    set Q := ∏ w ∈ S, m0 w (B w) with hQ
    set a := mi0 A with ha
    set L := m0 v (latV b v) with hLdef
    have hQ0 : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => hB0 w
    have hQt : Q ≠ ⊤ := ENNReal.prod_ne_top fun w _ => hBt w
    have hP0 : a * Q ≠ 0 := mul_ne_zero hA0 hQ0
    have hPt : a * Q ≠ ⊤ := ENNReal.mul_ne_top hAt hQt
    have e4 : (cS S : ℝ≥0∞) * (a * Q) = ((cS (insert v S) : ℝ≥0∞) * L) * (a * Q) := by
      rw [e2]; ring
    have e5 := (ENNReal.mul_left_inj hP0 hPt).mp e4
    have e6 := congrArg ENNReal.toReal e5
    simpa [ENNReal.toReal_mul] using e6
  obtain ⟨c, S₀, -, hS₀⟩ := GlobalTheory.T.infinite_product_renormalization _ (fun v => (m0 v (latV b v)).toReal) cS ∅
    (fun _ => ENNReal.toReal_nonneg) hsum hstep
  have hc : IsEulerProd b I c mi0 m0 := by
    refine ⟨hfin, hsum, S₀, fun S hS φinf φ hφi hφ => ?_⟩
    refine (hcS S φinf φ hφi hφ).trans ?_
    have hcS' : (cS S : ℝ≥0∞) = (c : ℝ≥0∞) *
        ENNReal.ofReal (∏' v : {v // v ∉ S}, (m0 v.1 (latV b v.1)).toReal) := by
      rw [← ENNReal.ofReal_coe_nnreal (p := cS S), (hS₀ S hS).2, ENNReal.ofReal_mul (NNReal.coe_nonneg _),
        ENNReal.ofReal_coe_nnreal]
    rw [hcS']
    ring
  suffices h : c = 1 from h ▸ hc
  obtain ⟨φ, C, φc, φp, φf, hb⟩ := GlobalTheory.T.global_volume_rank_one_normalised F E σ hcm M J hJ hM h₀ d b li lam hli hlam μ 𝓕 hμ h𝓕 mi hmi m hm
  obtain ⟨hdf, κ, hκ, hg⟩ := GlobalTheory.T.finite_volume_rank_one_euler F E σ hcm M J hJ hM h₀ d b lam hlam m hm nzv
  have : BorelSpace (Fin 1 → Fin M → Ainf F ⊗[F] E) := by
    have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
    obtain ⟨_, _, _, _, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hcm.1
    exact (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Ainf F)).2.2.2.2.2.2.2.1 1 M
  have hφm : Measurable fun X => ENNReal.ofReal (φ X) := φc.measurable.ennreal_ofReal
  set w := ∫⁻ X, ENNReal.ofReal (φ X) ∂mi0 with hw
  have hw0 : 0 < w.toReal := ENNReal.toReal_pos (fun h => nzi (by
    rw [hw, lintegral_eq_zero_iff hφm] at h
    exact ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 (h.mono fun X hX =>
      (ENNReal.ofReal_pos.2 (φp X)).ne' hX)))) φf.ne
  have key : ∀ k : ℕ, ∃ a : ℕ, k < a ∧ |(c : ℝ) - 1| * (w.toReal * κ) * (a : ℝ) ≤ |C| := fun k => by
    obtain ⟨a, ha, h1⟩ := hg k
    have ha0 : 0 < a := lt_of_le_of_lt k.zero_le ha
    have haE : (a : E) ≠ 0 := by exact_mod_cast ha0.ne'
    obtain ⟨I', e1, e2⟩ := hb a ha0
    have hA : ∀ v, MeasurableSet {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v} := fun v => by
      have hR := GlobalTheory.T.completion_is_local_ring F v
      obtain ⟨_, _, _, _, -⟩ := hR
      have : BorelSpace (Fv F v) := ⟨rfl⟩
      obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Fv F v)
      have := hB 1 M
      have hu : IsUnit (a : Fv F v ⊗[F] E) := by simpa using (Ne.isUnit haE).map (inclR (F := F) (Fv F v))
      have hK : IsCompact {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v} :=
        (Homeomorph.smul hu.unit).isCompact_preimage.2 ((GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 M).2.2.2.1 v).1
      exact hK.measurableSet
    obtain ⟨-, e3⟩ := GlobalTheory.T.euler_product_measure_integral F E σ hcm d b 1 M _ c _ _ hc _ _ hφm (fun v => hA v) (fun v => hdf a ha0 v)
      (((GlobalTheory.T.lattice_stable_almost_everywhere F E σ hcm d b 1 M).1 (Matrix.of fun _ _ => (a : E)) ((Matrix.det_unique _).trans_ne haE)).mono fun v hv => Set.ext fun X => by
        refine Iff.trans (Iff.of_eq (congrArg (· ∈ latV b v) (funext fun p => funext fun i => ?_))) (hv X)
        rw [Subsingleton.elim p 0]
        simp [rmul, mul_comm])
    generalize (∏' v, (m0 v {X : Fin 1 → Fin M → Fv F v ⊗[F] E |
      (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}).toReal) = P at h1 e2 e3
    have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha0
    have hP : 0 ≤ P := le_trans (by positivity) h1
    have e4 := congrArg ENNReal.toReal (e1.symm.trans e3)
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hP, ENNReal.coe_toReal, ENNReal.coe_toReal] at e4
    rw [e4, show (c : ℝ) * w.toReal * P - w.toReal * P = (c - 1) * (w.toReal * P) by ring, abs_mul,
      abs_of_nonneg (mul_nonneg hw0.le hP)] at e2
    have hD : 0 < Module.finrank ℚ F := Module.finrank_pos
    have h2 : (a : ℝ) * (a : ℝ) ^ (Module.finrank ℚ F * M) ≤ (a : ℝ) ^ (Module.finrank ℚ F * (2 * M - 2)) := by
      rw [← pow_succ']
      refine pow_le_pow_right₀ haR ?_
      obtain ⟨M', rfl⟩ := Nat.exists_eq_add_of_le' hM
      rw [show 2 * (M' + 3) - 2 = M' + 3 + (M' + 1) by omega, mul_add _ (M' + 3)]
      exact Nat.add_le_add_left (Nat.mul_pos hD (Nat.succ_pos _)) _
    refine ⟨a, ha, le_of_mul_le_mul_right ?_ (show (0 : ℝ) < (a : ℝ) ^ (Module.finrank ℚ F * M) by positivity)⟩
    calc _ = |(c : ℝ) - 1| * (w.toReal * (κ * ((a : ℝ) * (a : ℝ) ^ (Module.finrank ℚ F * M)))) := by ring
      _ ≤ |(c : ℝ) - 1| * (w.toReal * P) := by
          gcongr
          exact (mul_le_mul_of_nonneg_left h2 hκ.le).trans h1
      _ ≤ _ := e2.trans (by gcongr; exact le_abs_self C)
  by_contra hne'
  have hp : 0 < |(c : ℝ) - 1| * (w.toReal * κ) :=
    mul_pos (abs_pos.2 (sub_ne_zero.2 (by exact_mod_cast hne'))) (mul_pos hw0 hκ)
  obtain ⟨k, hk⟩ := exists_nat_gt (|C| / (|(c : ℝ) - 1| * (w.toReal * κ)))
  obtain ⟨a, ha, h⟩ := key k
  rw [div_lt_iff₀' hp] at hk
  have : (k : ℝ) < a := by exact_mod_cast ha
  nlinarith

end GlobalTheory.CompanionTheory.SW.OneZero
