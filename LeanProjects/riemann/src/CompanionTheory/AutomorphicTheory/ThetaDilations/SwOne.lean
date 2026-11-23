import CompanionTheory.AutomorphicTheory.ThetaDilations.ThetaFin
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyRealStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianOneByOneIsScalarStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilFormulaRangeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureZeroStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureIntegralStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainRankOneDensityStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneLocalDensitiesProductConvergesStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjectionsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresContinuityStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeStableAlmostEverywhereStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace CompanionTheory.PlacePermOperatorBicommutantSpan

set_option maxHeartbeats 600000 in
theorem sw_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (T : Matrix (Fin 1) (Fin 1) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → SWMeas σ J T hT := by
  intro F E _ _ _ _ _ σ hcm M J hJ hM T hT hd d b li lam hli hlam μ 𝓕 hμ h𝓕 mi m hmi hm
  obtain ⟨t1, t2⟩ := theta_inv F E σ hcm M J hJ μ 𝓕 hμ h𝓕 1 T
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_isEulerProd_of_invariant_of_fiber_supported F E σ hcm M J hJ 1 (Or.inr hM) T hT hd d b li lam hli hlam mi hmi m hm _
    (theta_measure_locally_finite F E σ hcm M J hJ hM μ 𝓕 hμ h𝓕 T hT hd) t1 t2
  by_cases h0 : mi (hermOf (Ainf F) σ T hT) = 0 ∨ ∃ v, m v (hermOf (Fv F v) σ T hT) = 0
  · rw [(GlobalTheory.T.euler_product_measure_zero F E σ hcm d b 1 M _ c _ _).2.1 hc h0]
    exact (GlobalTheory.T.euler_product_measure_zero F E σ hcm d b 1 M 0 1 _ _).2.2 hc.1 hc.2.1 h0
  suffices h : c = 1 from h ▸ hc
  obtain ⟨β, rfl, hβ, he⟩ := GlobalTheory.T.hermitian_one_by_one_is_scalar F E σ hcm T hT
  simp only [he] at hc h0
  push Not at h0
  obtain ⟨φ, C, φc, φp, φf, hb⟩ := GlobalTheory.T.thetaMeas_rank_one_sub_density_product_le F E σ hcm M J hJ hM d b li lam hli hlam μ 𝓕 hμ h𝓕 mi hmi m hm β (hβ hd)
  obtain ⟨κ, hκ, hg⟩ := GlobalTheory.T.exists_frequently_mul_pow_le_tprod_rank_one_local_density F E σ hcm M J hJ hM d b lam hlam m hm β (hβ hd) h0.2
  have : BorelSpace (Fin 1 → Fin M → Ainf F ⊗[F] E) := by
    have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
    obtain ⟨_, _, _, _, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hcm.1
    exact (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Ainf F)).2.2.2.2.2.2.2.1 1 M
  have hφm : Measurable fun X => ENNReal.ofReal (φ X) := φc.measurable.ennreal_ofReal
  set w := ∫⁻ X, ENNReal.ofReal (φ X) ∂(mi (hermScal (Ainf F) σ (algebraMap F _ β))) with hw
  have hw0 : 0 < w.toReal := ENNReal.toReal_pos (fun h => h0.1 (by
    rw [hw, lintegral_eq_zero_iff hφm] at h
    exact ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 (h.mono fun X hX =>
      (ENNReal.ofReal_pos.2 (φp X)).ne' hX)))) φf.ne
  have key : ∀ k : ℕ, ∃ a : ℕ, k < a ∧ |(c : ℝ) - 1| * (w.toReal * κ) * (a : ℝ) ≤ |C| := fun k => by
    obtain ⟨a, ha, h1⟩ := hg k
    have ha0 : 0 < a := lt_of_le_of_lt k.zero_le ha
    have haE : (a : E) ≠ 0 := by exact_mod_cast ha0.ne'
    obtain ⟨I, e1, e2⟩ := hb a ha0
    have hA : ∀ v, MeasurableSet {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v} ∧
        m v (hermScal (Fv F v) σ (algebraMap F _ β))
          {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v} < ⊤ := fun v => by
      have hR := GlobalTheory.T.completion_is_local_ring F v
      have hR' := hR
      obtain ⟨_, _, _, _, -⟩ := hR'
      have : BorelSpace (Fv F v) := ⟨rfl⟩
      obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Fv F v)
      have := hB 1 M
      have hu : IsUnit (a : Fv F v ⊗[F] E) := by simpa using (Ne.isUnit haE).map (inclR (F := F) (Fv F v))
      have hK : IsCompact {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v} :=
        (Homeomorph.smul hu.unit).isCompact_preimage.2 ((GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 M).2.2.2.1 v).1
      obtain ⟨-, k1, k2⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hcm (Fv F v) d b (lam v) (hlam v).1
      have := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hcm M J hJ (Fv F v) hR 1 _ _ _ (k1 1 M) (k2 1) (hm v)
        (hermScal (Fv F v) σ (algebraMap F _ β))).1
      exact ⟨hK.measurableSet, hK.measure_lt_top⟩
    obtain ⟨-, e3⟩ := GlobalTheory.T.euler_product_measure_integral F E σ hcm d b 1 M _ c _ _ hc _ _ hφm (fun v => (hA v).1) (fun v => (hA v).2)
      (((GlobalTheory.T.lattice_stable_almost_everywhere F E σ hcm d b 1 M).1 (Matrix.of fun _ _ => (a : E)) ((Matrix.det_unique _).trans_ne haE)).mono fun v hv => Set.ext fun X => by
        refine Iff.trans (Iff.of_eq (congrArg (· ∈ latV b v) (funext fun p => funext fun i => ?_))) (hv X)
        rw [Subsingleton.elim p 0]
        simp [rmul, mul_comm])
    generalize (∏' v, (m v (hermScal (Fv F v) σ (algebraMap F _ β)) {X : Fin 1 → Fin M → Fv F v ⊗[F] E |
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
  by_contra hne
  have hp : 0 < |(c : ℝ) - 1| * (w.toReal * κ) :=
    mul_pos (abs_pos.2 (sub_ne_zero.2 (by exact_mod_cast hne))) (mul_pos hw0 hκ)
  obtain ⟨k, hk⟩ := exists_nat_gt (|C| / (|(c : ℝ) - 1| * (w.toReal * κ)))
  obtain ⟨a, ha, h⟩ := key k
  rw [div_lt_iff₀' hp] at hk
  have : (k : ℝ) < a := by exact_mod_cast ha
  nlinarith

end CompanionTheory.PlacePermOperatorBicommutantSpan
