import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm
import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalHHermScal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatrixEulerProductStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.MassSimil.ScalModule

theorem map_eq_sqrt_smul {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (e : G ≃ₜ+ G) (ν : Measure G) [ν.IsAddHaarMeasure] (c : ℝ≥0)
    (h : ν.map (e ∘ e) = c • ν) : ν.map e = NNReal.sqrt c • ν := by
  haveI : (ν.map e).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν e
  obtain ⟨b, hb⟩ : ∃ b : ℝ≥0, ν.map e = b • ν :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul (ν.map e) ν⟩
  have he : Measurable e := e.continuous.measurable
  have h2 : ν.map (e ∘ e) = (b * b) • ν := by
    rw [← Measure.map_map he he, hb, Measure.map_smul, hb, smul_smul]
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : G)
  have hpos : ν K ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hK0).ne'
  have hfin : ν K ≠ ∞ := hK.measure_lt_top.ne
  have hbc : b * b = c := by
    have h3 : ((b * b : ℝ≥0) • ν) K = (c • ν) K := by rw [← h2, h]
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h3
    exact_mod_cast (ENNReal.mul_left_inj hpos hfin).1 h3
  rw [hb, ← hbc, NNReal.sqrt_mul_self]

theorem scalH_scalH {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {n : ℕ} (a b : R) (S : HermR R σ n) :
    scalH R σ a (scalH R σ b S) = scalH R σ (a * b) S := by
  apply Subtype.ext
  simp only [scalH_coe, smul_smul, map_mul]

theorem scalH_one {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {n : ℕ} (S : HermR R σ n) : scalH R σ 1 S = S := by
  apply Subtype.ext
  simp only [scalH_coe, map_one, one_smul]

def scalEquiv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    (n : ℕ) (l : F) (hl : l ≠ 0) : HermR R σ n ≃ₜ+ HermR R σ n :=
  have hc : ∀ a : R, Continuous (scalH R σ (n := n) a) := fun a => by
    obtain ⟨iTR, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
    haveI := iTR
    exact Continuous.subtype_mk ((continuous_const_smul _).comp continuous_subtype_val) _
  have hm : algebraMap F R l * algebraMap F R l⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hl, map_one]
  { toFun := scalH R σ (algebraMap F R l)
    invFun := scalH R σ (algebraMap F R l⁻¹)
    left_inv := fun S => by rw [scalH_scalH, mul_comm, hm, scalH_one]
    right_inv := fun S => by rw [scalH_scalH, hm, scalH_one]
    map_add' := fun S T => by
      apply Subtype.ext
      simp [scalH_coe]
    continuous_toFun := hc _
    continuous_invFun := hc _ }

def oneByOne {F E : Type} [Field F] [Field E] [Algebra F E] (l : F) : Matrix (Fin 1) (Fin 1) E :=
  Matrix.of fun _ _ => algebraMap F E l

theorem action_eq {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (l : F) (S : HermR R σ 1) :
    ((scalH R σ (algebraMap F R l) (scalH R σ (algebraMap F R l) S) : HermR R σ 1) :
        Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) =
      cT (sigR R σ) ((oneByOne l : Matrix (Fin 1) (Fin 1) E).map (inclR R)) *
        (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) *
        (oneByOne l : Matrix (Fin 1) (Fin 1) E).map (inclR R) := by
  have h1 : inclR R (algebraMap F E l) = algebraMap R (R ⊗[F] E) (algebraMap F R l) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes l
  have h2 : sigR R σ (algebraMap R (R ⊗[F] E) (algebraMap F R l)) =
      algebraMap R (R ⊗[F] E) (algebraMap F R l) := by
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]
  ext i j
  simp only [scalH_coe, cT, oneByOne, Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Matrix.of_apply, Finset.univ_unique, Finset.sum_singleton, smul_eq_mul, h1, h2]
  have hi : i = default := Subsingleton.elim _ _
  have hj : j = default := Subsingleton.elim _ _
  subst hi hj
  ring

theorem local_scal {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (hR : IsLocR R) (l : F) (hl : l ≠ 0) (c : ℝ≥0)
    (ν : Measure (HermR R σ 1)) (hν : ν.IsAddHaarMeasure)
    (h : ∀ τ : HermR R σ 1 → HermR R σ 1, (∀ S, (τ S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) =
      cT (sigR R σ) ((oneByOne l : Matrix (Fin 1) (Fin 1) E).map (inclR R)) *
        (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) *
        (oneByOne l : Matrix (Fin 1) (Fin 1) E).map (inclR R)) → ν.map τ = c • ν) :
    ν.map (scalH R σ (algebraMap F R l)) = NNReal.sqrt c • ν := by
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨iTR, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
  haveI := iTR
  obtain ⟨jLC, jSC, jT2, jB, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hcm R 1
  haveI := jLC
  haveI := jSC
  haveI := jT2
  haveI := jB
  exact map_eq_sqrt_smul (scalEquiv σ hcm R 1 l hl) ν c (h _ (action_eq R σ l))

theorem scal_module : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ l : F, l ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ ν : Measure (HermR (Ainf F) σ 1), ν.IsAddHaarMeasure → ν.map (GlobalTheory.CompanionTheory.SW.MassSimil.scalH (Ainf F) σ (algebraMap F (Ainf F) l)) = cinf • ν) ∧ ∀ v : HeightOneSpectrum (𝓞 F), ∀ ν : Measure (HermR (Fv F v) σ 1), ν.IsAddHaarMeasure → ν.map (GlobalTheory.CompanionTheory.SW.MassSimil.scalH (Fv F v) σ (algebraMap F (Fv F v) l)) = c v • ν := by
  intro F E _ _ _ _ _ σ hcm l hl
  have hdet : (oneByOne l : Matrix (Fin 1) (Fin 1) E).det ≠ 0 := by
    rw [Matrix.det_fin_one]
    exact (map_ne_zero (algebraMap F E)).2 hl
  obtain ⟨ci, c, hu, hi, hv⟩ := GlobalTheory.T.hermitian_matrix_euler_product F E σ hcm 1 (oneByOne l) hdet
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  refine ⟨NNReal.sqrt ci, fun v => NNReal.sqrt (c v), (PositivityTheory.PlacePermOperatorBicommutantSpan.up_alg F ci ci c c hu hu).2.2.2.2.2.1, ?_, ?_⟩
  · intro ν hν
    exact local_scal σ hcm (Ainf F) (GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hcm.1) l hl ci ν hν (hi ν hν)
  · intro v ν hν
    exact local_scal σ hcm (Fv F v) (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v) l hl (c v) ν hν (hv v ν hν)

end GlobalTheory.CompanionTheory.SW.MassSimil.ScalModule

end
