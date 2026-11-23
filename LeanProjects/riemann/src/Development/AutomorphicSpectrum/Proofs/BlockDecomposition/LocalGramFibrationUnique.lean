import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitsOpenEmbeddingLocalTensor
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramRightActionIdentities
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyRealStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolumeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresSupportStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal NNReal Topology

namespace GlobalTheory.CompanionTheory.SW.FibSch

theorem fib_scale_core (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [MeasurableSpace R] [BorelSpace R] (hR : GlobalTheory.CompanionTheory.SW.IsLocR R) (n : ℕ)
    (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n))
    (m : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (hμ : μ.IsAddHaarMeasure) (hν : ν.IsAddHaarMeasure) (hm : GlobalTheory.CompanionTheory.SW.IsGramFib R σ J n μ ν m)
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (hg : IsUnit g.det) :
    ∃ κ : ℝ≥0, κ ≠ 0 ∧ ∀ S S' : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n,
      (S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
        HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g →
      m S' = κ • (m S).map (fun X => GlobalTheory.CompanionTheory.SW.rmul R X g) := by
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨hTK, hLK, hSK, hTK2, -, -, -, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R
  haveI := hTK
  haveI := hLK
  haveI := hSK
  haveI := hTK2
  haveI := hBor n M
  obtain ⟨hLH, hSH, hT2H, hBH, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n
  haveI := hLH
  haveI := hSH
  haveI := hT2H
  haveI := hBH
  obtain ⟨-, hcomp, hone, hmem, -⟩ := GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra F E σ hσ M J hJ R n
  have hg1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hg
  have hg2 : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hg
  have hrc : ∀ h : Matrix (Fin n) (Fin n) (R ⊗[F] E),
      Continuous fun X : Fin n → Fin M → R ⊗[F] E => GlobalTheory.CompanionTheory.SW.rmul R X h := by
    intro h
    refine continuous_pi fun b => continuous_pi fun i => ?_
    simp only [GlobalTheory.CompanionTheory.SW.rmul]
    refine continuous_finset_sum _ fun k _ => ?_
    have h1 : Continuous fun Y : Fin n → Fin M → R ⊗[F] E => Y k i :=
      (continuous_apply i).comp (continuous_apply k)
    exact h1.mul continuous_const
  let e : (Fin n → Fin M → R ⊗[F] E) ≃+ (Fin n → Fin M → R ⊗[F] E) :=
    { toFun := fun X => GlobalTheory.CompanionTheory.SW.rmul R X g
      invFun := fun X => GlobalTheory.CompanionTheory.SW.rmul R X g⁻¹
      left_inv := fun X => by simp only [hcomp, hg1, hone]
      right_inv := fun X => by simp only [hcomp, hg2, hone]
      map_add' := fun X Y => by
        funext b i
        simp only [GlobalTheory.CompanionTheory.SW.rmul, Pi.add_apply, add_mul, Finset.sum_add_distrib] }
  have hc1 : HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ)
      (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = 1 := by
    unfold HeckeCharacterZeroLocus.SiegelWeilU.cT
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  have key : ∀ (h h' A : Matrix (Fin n) (Fin n) (R ⊗[F] E)), h * h' = 1 →
      HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) h' *
        (HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) h * A * h) * h' = A := by
    intro h h' A hh
    have h1 : HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) h' *
        HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) h = 1 := by
      rw [← HeckeCharacterZeroLocus.SiegelWeilU.cT_mul, hh, hc1]
    calc HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) h' *
          (HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) h * A * h) * h'
        = (HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) h' *
            HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) h) * A * (h * h') := by
          simp only [Matrix.mul_assoc]
      _ = A := by rw [h1, hh, Matrix.one_mul, Matrix.mul_one]
  have hcj : ∀ h : Matrix (Fin n) (Fin n) (R ⊗[F] E),
      Continuous fun S : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n =>
        HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) h *
          (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * h := fun h =>
    (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  let t : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n ≃+ HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n :=
    { toFun := fun S => ⟨HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) g *
        (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g, hmem S g⟩
      invFun := fun S => ⟨HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) g⁻¹ *
        (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g⁻¹, hmem S g⁻¹⟩
      left_inv := fun S => Subtype.ext (key _ _ _ hg1)
      right_inv := fun S => Subtype.ext (key _ _ _ hg2)
      map_add' := fun S T => Subtype.ext (by
        simp only [AddSubgroup.coe_add, Matrix.mul_add, Matrix.add_mul]) }
  have hec : Continuous e := hrc g
  have hes : Continuous e.symm := hrc g⁻¹
  have htc : Continuous t := (hcj g).subtype_mk _
  have hts : Continuous t.symm := (hcj g⁻¹).subtype_mk _
  haveI hμe : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ hec hes
  haveI hνt : (ν.map t).IsAddHaarMeasure := t.isAddHaarMeasure_map ν htc hts
  obtain ⟨a, ha0, hmu⟩ : ∃ a : ℝ≥0, a ≠ 0 ∧ μ.map e = a • μ :=
    ⟨_, (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map e) μ).ne',
      Measure.isAddLeftInvariant_eq_smul _ _⟩
  obtain ⟨c, hc0, hnu⟩ : ∃ c : ℝ≥0, c ≠ 0 ∧ ν.map t = c • ν :=
    ⟨_, (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (ν.map t) ν).ne',
      Measure.isAddLeftInvariant_eq_smul _ _⟩
  have hfib := GlobalTheory.T.gram_fiber_measures_rmul_equivariant F E σ hσ M J hJ R hR n μ ν m hμ hν hm g hg t (fun _ => rfl) a c hmu hnu
  refine ⟨c / a, div_ne_zero hc0 ha0, fun S S' hS => ?_⟩
  have hS' : S' = t S := Subtype.ext hS
  have h := hfib S
  rw [← hS'] at h
  calc m S' = a⁻¹ • (a • m S') := by rw [smul_smul, inv_mul_cancel₀ ha0, one_smul]
    _ = (c / a) • (m S).map (fun X => GlobalTheory.CompanionTheory.SW.rmul R X g) := by
      rw [h, smul_smul, div_eq_inv_mul]

theorem fib_scale : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], GlobalTheory.CompanionTheory.SW.IsLocR R → ∀ (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → GlobalTheory.CompanionTheory.SW.IsGramFib R σ J n μ ν m → ∀ (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)), IsUnit g.det → ∃ κ : ℝ≥0, κ ≠ 0 ∧ ∀ S S' : HermR R σ n, (S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = HeckeCharacterZeroLocus.SiegelWeilU.cT (sigR R σ) g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g → m S' = κ • (m S).map (fun X => GlobalTheory.CompanionTheory.SW.rmul R X g) := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR n μ ν m hμ hν hm g hg
  exact fib_scale_core F E σ hσ M J hJ R hR n μ ν m hμ hν hm g hg

end GlobalTheory.CompanionTheory.SW.FibSch
