import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EMatMulNegCol
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FibreMassEq
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.AvgFree.ElemHerm

theorem cjPre_haar (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    [MeasurableSpace R] [BorelSpace R] (n : ℕ) (ν : Measure (HermR R σ n)) (hν : ν.IsAddHaarMeasure)
    (O : Subring (R ⊗[F] E)) (hOc : IsCompact (O : Set (R ⊗[F] E))) (hOo : IsOpen (O : Set (R ⊗[F] E)))
    (hOs : ∀ x ∈ O, sigR R σ x ∈ O) (g g' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (hgg : g * g' = 1)
    (hg : ∀ i j, g i j ∈ O) (hg' : ∀ i j, g' i j ∈ O) (Y : Set (HermR R σ n)) (hY : MeasurableSet Y) :
    MeasurableSet (cjPre R σ g Y) ∧ ν (cjPre R σ g Y) = ν Y := by
  obtain ⟨hTK, hLK, hSK, hTK2, hsc, -, -, -, hcl, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R
  haveI := hTK
  haveI := hLK
  haveI := hSK
  haveI := hTK2
  obtain ⟨hLH, hSH, hT2H, hBH, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n
  haveI := hLH
  haveI := hSH
  haveI := hT2H
  haveI := hBH
  have hinv : ∀ x, sigR R σ (sigR R σ x) = x :=
    GlobalTheory.CompanionTheory.AvgFree.sigR_sigR R σ (GlobalTheory.CompanionTheory.SW.HermTop.sigma_sigma hσ)
  have hg2 : g' * g = 1 := mul_eq_one_comm.mp hgg
  let t : HermR R σ n ≃+ HermR R σ n :=
    { toFun := fun S => ⟨cjM R σ g S, cjM_mem R σ hinv g S S.2⟩
      invFun := fun S => ⟨cjM R σ g' S, cjM_mem R σ hinv g' S S.2⟩
      left_inv := fun S => Subtype.ext (by
        show cjM R σ g' (cjM R σ g S) = S
        rw [← cjM_mul, hgg, cjM_one])
      right_inv := fun S => Subtype.ext (by
        show cjM R σ g (cjM R σ g' S) = S
        rw [← cjM_mul, hg2, cjM_one])
      map_add' := fun S T => Subtype.ext (by
        simp only [cjM, AddSubgroup.coe_add, Matrix.mul_add, Matrix.add_mul]) }
  have hcj : ∀ h : Matrix (Fin n) (Fin n) (R ⊗[F] E),
      Continuous fun S : HermR R σ n => cjM R σ h (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := fun h =>
    (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  have htc : Continuous t := (hcj g).subtype_mk _
  have hts : Continuous t.symm := (hcj g').subtype_mk _
  have hpre : ∀ Z : Set (HermR R σ n), cjPre R σ g Z = t ⁻¹' Z := by
    intro Z
    ext y
    constructor
    · rintro ⟨z, hz, e⟩
      have : t y = z := Subtype.ext e
      show t y ∈ Z
      rwa [this]
    · intro h
      exact ⟨t y, h, rfl⟩

  have hent : ∀ (h : Matrix (Fin n) (Fin n) (R ⊗[F] E)), (∀ i j, h i j ∈ O) →
      ∀ y : Matrix (Fin n) (Fin n) (R ⊗[F] E), (∀ i j, y i j ∈ O) → ∀ i j, cjM R σ h y i j ∈ O := by
    intro h hh y hy i j
    simp only [cjM, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    exact O.sum_mem fun k _ => O.mul_mem (O.sum_mem fun m _ => O.mul_mem (hOs _ (hh _ _)) (hy _ _)) (hh _ _)
  let C : Set (HermR R σ n) := {y | ∀ i j, (y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j ∈ O}
  have hCv : C = Subtype.val ⁻¹'
      (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => (O : Set (R ⊗[F] E)) :
        Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
    ext y
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
  have hCc : IsCompact C := by
    rw [hCv]
    exact (hcl n).isClosedEmbedding_subtypeVal.isCompact_preimage
      (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hOc)
  have hCo : IsOpen C := by
    have hval : Continuous fun y : HermR R σ n => (y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
      continuous_subtype_val
    have e : C = ⋂ i, ⋂ j, {y : HermR R σ n | (y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j ∈ O} := by
      ext y
      simp only [C, Set.mem_iInter, Set.mem_setOf_eq]
    rw [e]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hOo.preimage ((continuous_apply_apply i j).comp hval)
  have hC0 : (0 : HermR R σ n) ∈ C := fun i j => O.zero_mem
  have htC : t ⁻¹' C = C := by
    ext y
    constructor
    · intro h
      have e : t.symm (t y) = y := t.symm_apply_apply y
      rw [← e]
      exact hent g' hg' _ h
    · intro h
      exact hent g hg _ h
  haveI hνt : (ν.map t).IsAddHaarMeasure := t.isAddHaarMeasure_map ν htc hts
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, ν.map t = c • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  have hCpos : ν C ≠ 0 := hCo.measure_ne_zero ν ⟨0, hC0⟩
  have hCfin : ν C ≠ ⊤ := hCc.measure_lt_top.ne
  have hc1 : c = 1 := by
    have h1 : ν.map t C = ν C := by
      rw [Measure.map_apply htc.measurable hCo.measurableSet, htC]
    rw [hc, Measure.coe_nnreal_smul_apply] at h1
    have h2 : (c : ℝ≥0∞) * ν C = 1 * ν C := by
      rw [one_mul]
      exact h1
    have h3 := (ENNReal.mul_left_inj hCpos hCfin).1 h2
    exact_mod_cast h3
  refine ⟨?_, ?_⟩
  · rw [hpre]
    exact htc.measurable hY
  · rw [hpre, ← Measure.map_apply htc.measurable hY, hc, hc1, one_smul]

end GlobalTheory.CompanionTheory.AvgFree.ElemHerm

theorem GlobalTheory.CompanionTheory.AvgFree.ElemHerm.coordHerm_cjPre_eMat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ O : Subring (Fv F v ⊗[F] E), IsCompact (O : Set (Fv F v ⊗[F] E)) → IsOpen (O : Set (Fv F v ⊗[F] E)) → (∀ x ∈ O, HeckeCharacterZeroLocus.SiegelWeilU.sigR (Fv F v) σ x ∈ O) → ∀ (n : ℕ) (l : Fin n) (a : Fin n → (Fv F v ⊗[F] E)), (∀ i, a i ∈ O) → a l = 1 → ∀ Y : Set (HermR (Fv F v) σ n), MeasurableSet Y → MeasurableSet (cjPre (Fv F v) σ (eMat (Fv F v) l a) Y) ∧ (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) (cjPre (Fv F v) σ (eMat (Fv F v) l a) Y) = (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) Y := by
  intro F E _ _ _ _ _ σ hσ d b v lv hlv O hOc hOo hOs n l a ha hl Y hY
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := hlv.1
  obtain ⟨-, -, hH⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lv hlv.1
  have he : ∀ (w : Fin n → Fv F v ⊗[F] E), (∀ i, w i ∈ O) → ∀ i j, eMat (Fv F v) l w i j ∈ O := by
    intro w hw i j
    simp only [eMat, Matrix.updateCol_apply, Matrix.one_apply]
    split_ifs
    · exact hw i
    · exact O.one_mem
    · exact O.zero_mem
  have hn : ∀ i, negCol (Fv F v) l a i ∈ O := by
    intro i
    simp only [negCol]
    split_ifs
    · exact O.one_mem
    · exact O.neg_mem (ha i)
  exact GlobalTheory.CompanionTheory.AvgFree.ElemHerm.cjPre_haar F E σ hσ (Fv F v) n _ (hH n) O hOc hOo hOs _ _
    (eMat_mul_negCol (Fv F v) l a hl) (he a ha) (he _ hn) Y hY
