import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.TupOfCv
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresSupportStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyRealStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolumeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoordinateMeasureScalingTensorStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianMeasureScalingTransformStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanFrameKTypeDecompositionStatement

open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal

noncomputable section
namespace GlobalTheory.CompanionTheory.BinaryDil

theorem fibre_unit_dilation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 0 < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)), laminf.IsAddHaarMeasure → ∀ (minf : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)), GlobalTheory.CompanionTheory.SW.IsGramFib (Ainf F) σ J 1 (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf 1 M) (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf 1) minf → ∀ (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → ∀ s t : Ainf F, IsUnit t → minf (GlobalTheory.CompanionTheory.SW.hermScal (Ainf F) σ (t ^ 2 * s)) = ((∏ w, ‖e t w‖₊) ^ (2 * M - 2)) • (minf (GlobalTheory.CompanionTheory.SW.hermScal (Ainf F) σ s)).map (fun X p i => algebraMap (Ainf F) (Ainf F ⊗[F] E) t * X p i) := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM d b lam hlam m hm e he s t ht
  have hloc : GlobalTheory.CompanionTheory.SW.IsLocR (Ainf F) := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hσ.1
  obtain ⟨i1, i2, i3, i4, i5, -, -, hB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Ainf F) d b lam hlam
  have hd : d = 2 := by
    rw [← hσ.2.2.1, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  set N : ℝ≥0 := ∏ w, ‖e t w‖₊ with hN
  have hN0 : N ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun w _ => ?_
    have : IsUnit (e t) := ht.map e
    exact nnnorm_ne_zero_iff.2 (Pi.isUnit_iff.1 this w).ne_zero
  have hN2 : ∏ w, ‖e (t ^ 2) w‖₊ = N ^ 2 := by
    rw [hN, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun w _ => ?_
    simp [map_pow]
  have hs1 := GlobalTheory.T.archimedean_haar_scaling_norm F e he lam hlam t ht
  have hs2 := GlobalTheory.T.archimedean_haar_scaling_norm F e he lam hlam (t ^ 2) (ht.pow 2)
  rw [hN2] at hs2
  have hk := GlobalTheory.T.coordinate_measure_scaling_tensor F E σ hσ M 2 b lam hlam t ht _ hs1
  let g : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E) := Matrix.of fun _ _ => algebraMap (Ainf F) (Ainf F ⊗[F] E) t
  have hg : IsUnit g.det := by
    rw [Matrix.det_fin_one]
    exact ht.map (algebraMap (Ainf F) (Ainf F ⊗[F] E))
  have hrm : (fun X : Fin 1 → Fin M → Ainf F ⊗[F] E => GlobalTheory.CompanionTheory.SW.rmul (Ainf F) X g) =
      fun X p i => algebraMap (Ainf F) (Ainf F ⊗[F] E) t * X p i := by
    funext X p i
    simp only [GlobalTheory.CompanionTheory.SW.rmul, Fin.sum_univ_one, g, Matrix.of_apply]
    rw [Subsingleton.elim p 0, mul_comm]
  have hsig : sigR (Ainf F) σ (algebraMap (Ainf F) (Ainf F ⊗[F] E) t) = algebraMap (Ainf F) (Ainf F ⊗[F] E) t := by
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]
  let τ : HermR (Ainf F) σ 1 → HermR (Ainf F) σ 1 := fun S =>
    ⟨fun i j => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t ^ 2) * (S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) i j, by
      intro i j
      have := S.2 i j
      show sigR (Ainf F) σ (_ * _) = _ * _
      rw [map_mul, this, map_pow, map_pow, hsig]⟩
  have hτe : ∀ S i j, (τ S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) i j =
      algebraMap (Ainf F) (Ainf F ⊗[F] E) (t ^ 2) * (S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) i j := fun _ _ _ => rfl
  have hτm : Measurable τ := by
    haveI : BorelSpace (HermR (Ainf F) σ 1) := ⟨rfl⟩
    have : Continuous τ := by
      refine Continuous.subtype_mk ?_ _
      refine continuous_pi fun i => continuous_pi fun j => ?_
      exact continuous_const.mul ((continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val))
    exact this.measurable
  have hc := GlobalTheory.T.hermitian_measure_scaling_transform F E σ hσ 2 b lam hlam (t ^ 2) (ht.pow 2) _ hs2 τ hτm hτe
  have hτ : ∀ S, (τ S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) = HeckeCharacterZeroLocus.SiegelWeilU.cT (sigR (Ainf F) σ) g * S * g := by
    intro S
    ext i j
    rw [hτe, map_pow, GlobalTheory.CompanionTheory.SW.Dil.cT_scalar _ _ hsig]
  have key := GlobalTheory.T.gram_fiber_measures_rmul_equivariant F E σ hσ M J hJ (Ainf F) hloc 1 (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam 1 M)
    (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam 1) m (hW 1 M) (hH 1) hm g hg τ hτ _ _
    (by rw [hrm]; exact hk) hc (GlobalTheory.CompanionTheory.SW.hermScal (Ainf F) σ s)
  have hτs : τ (GlobalTheory.CompanionTheory.SW.hermScal (Ainf F) σ s) = GlobalTheory.CompanionTheory.SW.hermScal (Ainf F) σ (t ^ 2 * s) := by
    apply Subtype.ext
    funext i j
    change algebraMap (Ainf F) (Ainf F ⊗[F] E) (t ^ 2) * (s ⊗ₜ[F] (1 : E)) = (t ^ 2 * s) ⊗ₜ[F] (1 : E)
    simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
  rw [hτs, hrm] at key
  have e1 : (N ^ (2 * M)) * (N⁻¹ ^ (2 * M)) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hN0, one_pow]
  have e2 : (N ^ (2 * M)) * (N ^ 2)⁻¹ = N ^ (2 * M - 2) := by
    obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
    have : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [this, pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hN0), mul_one]
    simp
  have key2 := congrArg (fun μ' => (N ^ (2 * M)) • μ') key
  simp only [smul_smul] at key2
  rw [e1, e2, one_smul] at key2
  exact key2

theorem dilation_inf_binary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (J : Matrix (Fin 2) (Fin 2) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (li : Measure (Ainf F)), IsStdInf li →
  ∀ (mi : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin 2 → Ainf F ⊗[F] E)),
  IsGramFib (Ainf F) σ J 1 (coordW (Ainf F) b li 1 2) (coordHerm (Ainf F) σ b li 1) mi →
  ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ ε : ℝ, 0 < ε → ∀ (s : Ainf F) (φ : (Fin 1 → Fin 2 → Ainf F ⊗[F] E) → ℝ), Continuous φ →
  ENNReal.ofReal (ε ^ (4 * Module.finrank ℚ F)) * ∫⁻ X, ENNReal.ofReal (φ (PositivityTheory.Rg.Mass.dil θ ε X)) ∂(mi (hermScal (Ainf F) σ s)) =
    ENNReal.ofReal ((ε ^ 2) ^ Module.finrank ℚ F) * ∫⁻ X, ENNReal.ofReal (φ X) ∂(mi (hermScal (Ainf F) σ (θ (ε ^ 2) * s))) := by
  intro F E _ _ _ _ _ σ hσ J hJ d b li hli mi hm θ hθ ε hε s φ hφ
  obtain ⟨-, e, -, he, -, habs, -⟩ := GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hσ.1
  obtain ⟨i1, i2, i3, i4, -, -, -, hB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  haveI : BorelSpace (Fin 1 → Fin 2 → Ainf F ⊗[F] E) := hB 1 2
  set t : Ainf F := θ ε with ht_def
  have ht : IsUnit t := (isUnit_iff_ne_zero.2 hε.ne').map θ
  have key := fibre_unit_dilation F E σ hσ 2 J hJ (by norm_num) d b li hli.1 mi hm e he s t ht
  set n := Module.finrank ℚ F with hn
  have hw : ∀ w, ‖e t w‖₊ = ε.toNNReal := by
    intro w
    have h1 := (PositivityTheory.PlacePermOperatorBicommutantSpan.theta_real F hσ.1).2 θ hθ ε w
    have h2 := habs t w
    apply NNReal.eq
    rw [coe_nnnorm, Real.norm_eq_abs, h2, Real.coe_toNNReal _ hε.le]
    rw [show ‖t w‖ = ‖θ ε w‖ from rfl, h1, abs_of_pos hε]
  have hN : ∏ w, ‖e t w‖₊ = ε.toNNReal ^ n := by
    have hc : Fintype.card (InfinitePlace F) = n := by
      have := hσ.1
      rw [hn, IsTotallyReal.finrank F, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
        IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
    rw [Finset.prod_congr rfl fun w _ => hw w, Finset.prod_const, Finset.card_univ, hc]
  have hs : θ (ε ^ 2) * s = t ^ 2 * s := by rw [map_pow]
  have hD : Continuous (fun (X : Fin 1 → Fin 2 → Ainf F ⊗[F] E) p i => algebraMap (Ainf F) (Ainf F ⊗[F] E) t * X p i) :=
    continuous_pi fun p => continuous_pi fun i =>
      continuous_const.mul ((continuous_apply i).comp (continuous_apply p))
  have hf : Measurable (fun X => ENNReal.ofReal (φ X)) := hφ.measurable.ennreal_ofReal
  rw [hs, key, lintegral_smul_measure, lintegral_map hf hD.measurable, hN]
  have hdil : ∀ X, PositivityTheory.Rg.Mass.dil θ ε X = fun p i => algebraMap (Ainf F) (Ainf F ⊗[F] E) t * X p i := by
    intro X
    funext p i
    simp [PositivityTheory.Rg.Mass.dil, Algebra.TensorProduct.algebraMap_apply, ht_def]
  simp only [hdil]
  rw [ENNReal.smul_def, smul_eq_mul, ← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [NNReal.coe_pow, Real.coe_toNNReal _ hε.le]
  ring

end GlobalTheory.CompanionTheory.BinaryDil

end
