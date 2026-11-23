import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm
import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalHHermScal
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitsOpenEmbeddingLocalTensor
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IsFibreFamilyTransport
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramRightActionIdentities
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresScaling
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresUniqueAe
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.FibSim

theorem conj_scal {A : Type} [CommRing A] {M n : ℕ} (C : Matrix (Fin n) (Fin M) A)
    (D : Matrix (Fin M) (Fin n) A) (G' G J : Matrix (Fin M) (Fin M) A) (t : A)
    (h : G' * J * G = t • J) : (C * G' * J) * (G * D) = t • (C * J * D) := by
  calc (C * G' * J) * (G * D) = C * (G' * J * G) * D := by simp only [Matrix.mul_assoc]
    _ = t • (C * J * D) := by rw [h, Matrix.mul_smul, Matrix.smul_mul]

theorem fib_similitude : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ (g : GL (Fin M) (R ⊗[F] E)) (l : R), IsUnit l → cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = (algebraMap R (R ⊗[F] E) l) • JR R J → ∀ a c : ℝ≥0, μ.map (actTup R g) = a • μ → ν.map (GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ l) = c • ν → ∀ S, (m S).map (actTup R g) = (a / c) • m (GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ l S) := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR n μ ν m hμ hν hm g l hl hgl a c hmu hnu S
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
  obtain ⟨hLH, hSH, hT2H, hBH, hG⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n
  haveI := hLH
  haveI := hSH
  haveI := hT2H
  haveI := hBH
  obtain ⟨G, hGc, hGe⟩ := hG M J hJ
  have hKu := GlobalTheory.CompanionTheory.SW.KUnits.units_val_isOpenEmbedding F E σ hσ R hR
  have hcont : ∀ h : GL (Fin M) (R ⊗[F] E),
      Continuous (actTup R h : (Fin n → Fin M → R ⊗[F] E) → (Fin n → Fin M → R ⊗[F] E)) := by
    intro h
    refine continuous_pi fun b => ?_
    exact continuous_const.matrix_mulVec (continuous_apply b)
  let e : (Fin n → Fin M → R ⊗[F] E) ≃ₜ (Fin n → Fin M → R ⊗[F] E) :=
    { toFun := actTup R g
      invFun := actTup R g⁻¹
      left_inv := fun X => by
        funext b
        simp [actTup, Matrix.mulVec_mulVec]
      right_inv := fun X => by
        funext b
        simp [actTup, Matrix.mulVec_mulVec]
      continuous_toFun := hcont g
      continuous_invFun := hcont g⁻¹ }
  obtain ⟨u, rfl⟩ := hl
  let am := algebraMap R (R ⊗[F] E)
  have hinv : ∀ (v w : Rˣ) (_ : (v : R) * w = 1) (A : HermR R σ n),
      GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ (v : R) (GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ (w : R) A) = A := by
    intro v w hvw A
    apply Subtype.ext
    rw [GlobalTheory.CompanionTheory.SW.MassSimil.scalH_coe, GlobalTheory.CompanionTheory.SW.MassSimil.scalH_coe, smul_smul, ← map_mul, hvw,
      map_one, one_smul]
  have hcs : ∀ v : R, Continuous (GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ v : HermR R σ n → HermR R σ n) := by
    intro v
    have hv : Continuous fun A : HermR R σ n => (A : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
      continuous_subtype_val
    exact (hv.const_smul (algebraMap R (R ⊗[F] E) v)).subtype_mk _
  let τh : HermR R σ n ≃ₜ HermR R σ n :=
    { toFun := GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ (u : R)
      invFun := GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ ((u⁻¹ : Rˣ) : R)
      left_inv := hinv _ _ (by simp)
      right_inv := hinv _ _ (by simp)
      continuous_toFun := hcs _
      continuous_invFun := hcs _ }
  let B : Set (HermR R σ n) := {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}
  have hBo : IsOpen B := by
    have : B = (fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) ⁻¹'
        Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
      ext S
      rfl
    rw [this]
    exact hKu.isOpen_range.preimage continuous_subtype_val.matrix_det
  have hdet : ∀ (v : Rˣ) (A : HermR R σ n), A ∈ B → GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ (v : R) A ∈ B := by
    intro v A hA
    show IsUnit ((GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ (v : R) A : HermR R σ n) :
      Matrix (Fin n) (Fin n) (R ⊗[F] E)).det
    rw [GlobalTheory.CompanionTheory.SW.MassSimil.scalH_coe, Matrix.det_smul]
    exact ((v.isUnit.map (algebraMap R (R ⊗[F] E))).pow _).mul hA
  have hBτ : τh '' B = B := by
    ext S'
    constructor
    · rintro ⟨S, hS, rfl⟩
      exact hdet _ _ hS
    · intro hS'
      exact ⟨τh.symm S', hdet _ _ hS', τh.apply_symm_apply _⟩
  have hU : G ⁻¹' B = {X | IsUnit (gramR R σ J X).det} := by
    ext X
    show IsUnit _ ↔ IsUnit _
    rw [hGe]
  have hfam : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val (G ⁻¹' B) ν B m := by
    rw [hU]
    exact hm
  have hgram : ∀ X : Fin n → Fin M → R ⊗[F] E, gramR R σ J (actTup R g X) =
      (algebraMap R (R ⊗[F] E) (u : R)) • gramR R σ J X := by
    intro X
    rw [GlobalTheory.CompanionTheory.SW.GramAlg.gramR_eq, GlobalTheory.CompanionTheory.SW.GramAlg.gramR_eq, GlobalTheory.CompanionTheory.SW.GramAlg.colM_actTup,
      cT_mul]
    exact conj_scal _ _ _ _ _ _ hgl
  have hcomm : ∀ X, G (e X) = τh (G X) := by
    intro X
    apply Subtype.ext
    show ((G (actTup R g X) : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
      ((GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ (u : R) (G X) : HermR R σ n) :
        Matrix (Fin n) (Fin n) (R ⊗[F] E))
    rw [← hGe, GlobalTheory.CompanionTheory.SW.MassSimil.scalH_coe, ← hGe]
    exact hgram X
  have htr := GlobalTheory.CompanionTheory.SW.isFibreFamily_transport _ _ _ μ ν (gramR R σ J) G Subtype.val
    Subtype.val_injective hGc hGe _ (gramR R σ J) G hGc hGe e τh hcomm B hBo m hfam
  rw [hBτ, hU] at htr
  have hmu' : μ.map e = a • μ := hmu
  have hnu' : ν.map τh = c • ν := hnu
  rw [hmu', hnu'] at htr
  have hnew : IsGramFib R σ J n (a • μ) (c • ν) (fun b => (m (τh.symm b)).map e) := htr
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h0 : μ.map e = 0 := by rw [hmu', zero_smul]
    have h1 : (μ.map e) Set.univ = μ Set.univ := by
      rw [e.measurableEmbedding.map_apply, Set.preimage_univ]
    rw [h0] at h1
    exact (isOpen_univ.measure_pos μ Set.univ_nonempty).ne h1
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h0 : ν.map τh = 0 := by rw [hnu', zero_smul]
    have h1 : (ν.map τh) Set.univ = ν Set.univ := by
      rw [τh.measurableEmbedding.map_apply, Set.preimage_univ]
    rw [h0] at h1
    exact (isOpen_univ.measure_pos ν Set.univ_nonempty).ne h1
  haveI hμa : (a • μ).IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul μ ha0
  haveI hνc : (c • ν).IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul ν hc0
  have hres := GlobalTheory.CompanionTheory.SW.Rescale.isGramFib_rescale F E σ hσ M J hJ R hR n μ ν m hμ hν hm a c ha0 hc0
  have huq := GlobalTheory.CompanionTheory.SW.GramFib.fibre_unique F E σ hσ M J hJ R hR n (a • μ) (c • ν) _ hμa hνc hres _ hnew (τh S)
  have hs : τh.symm (τh S) = S := τh.symm_apply_apply S
  simp only [hs] at huq
  exact huq.symm

end GlobalTheory.CompanionTheory.SW.FibSim
