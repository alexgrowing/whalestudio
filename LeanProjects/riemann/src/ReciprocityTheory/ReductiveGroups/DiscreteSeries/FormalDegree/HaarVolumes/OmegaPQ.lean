import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.DensOn
import Formalism.LocalRingCardinality.DataCD
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.OmegaPQB

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

variable {P Q : ℕ}

def gToLieMat (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool} (s : GCo ε) :
    Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ :=
  Matrix.reindex e.symm e.symm (gMat s)

theorem gToLieMat_mem (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) (s : GCo ε) :
    gToLieMat e s ∈ Formalism.BasicNotions.lieU P Q :=
  (OmegaPQAux.mem_reindex_iff e he1 he2 (gMat s)).2 (OmegaPQAux.gMat_mem s)

def gToLie (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) (s : GCo ε) :
    Formalism.BasicNotions.lieU P Q :=
  ⟨gToLieMat e s, gToLieMat_mem e he1 he2 s⟩

namespace OmegaPQAux

def gToLieL (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    GCo ε →ₗ[ℝ] Formalism.BasicNotions.lieU P Q where
  toFun := gToLie e he1 he2
  map_add' s t := by
    apply Subtype.ext
    ext i j
    simp [gToLie, gToLieMat, gMat_add]
  map_smul' c s := by
    apply Subtype.ext
    ext i j
    simp [gToLie, gToLieMat, gMat_smul]

theorem gToLieL_bij (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    Function.Bijective (gToLieL e he1 he2) := by
  have hre : ∀ M : Matrix (Fin n) (Fin n) ℂ,
      Matrix.reindex e e (Matrix.reindex e.symm e.symm M) = M := by
    intro M; rw [← Matrix.reindex_symm, Equiv.apply_symm_apply]
  constructor
  · intro s t h
    have h2 := congrArg (fun X : Formalism.BasicNotions.lieU P Q =>
      Matrix.reindex e e (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)) h
    simp only [gToLieL, LinearMap.coe_mk, AddHom.coe_mk, gToLie, gToLieMat, hre] at h2
    rw [← coordOf_gMat s, ← coordOf_gMat t, h2]
  · intro X
    set Y := Matrix.reindex e e (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) with hYdef
    have hX : Matrix.reindex e.symm e.symm Y = X := by
      rw [hYdef, ← Matrix.reindex_symm, Equiv.symm_apply_apply]
    have hY := (mem_reindex_iff e he1 he2 Y).1 (by rw [hX]; exact X.2)
    refine ⟨coordOf Y, Subtype.ext ?_⟩
    change Matrix.reindex e.symm e.symm (gMat (coordOf (ε := ε) Y)) = X
    rw [gMat_coordOf Y hY, hX]

end OmegaPQAux

theorem isOmegaLeb_gToLie (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    Formalism.BasicNotions.IsOmegaLeb (ENNReal.ofReal (2 ^ (n * (n - 1) / 2)) • Measure.map (gToLie e he1 he2) volume) := by
  have : BorelSpace (Formalism.BasicNotions.lieU P Q) := ⟨rfl⟩
  set Lin := LinearEquiv.ofBijective _ (OmegaPQAux.gToLieL_bij e he1 he2) with hLin
  set CL := Lin.toContinuousLinearEquiv with hCL
  have hcoe : (CL : GCo ε → Formalism.BasicNotions.lieU P Q) = gToLie e he1 he2 := rfl
  have hG : Measurable (gToLie e he1 he2) := by rw [← hcoe]; exact CL.continuous.measurable
  constructor
  · have hd : (volume : Measure (Fin n → ℝ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    have hk : (volume : Measure (KPair ε → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    have hp : (volume : Measure (PCoord ε → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    have hK : (volume : Measure (KCo ε)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
    have hGv : (volume : Measure (GCo ε)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
    have h1 := ContinuousLinearEquiv.isAddHaarMeasure_map CL (volume : Measure (GCo ε))
    rw [hcoe] at h1
    exact Measure.IsAddHaarMeasure.smul _ (by simp) ENNReal.ofReal_ne_top
  · have hSF : SigmaFinite (volume : Measure (GCo ε)) := Measure.prod.instSigmaFinite
    set c := ENNReal.ofReal (2 ^ (n * (n - 1) / 2)) with hc
    set E : Fin n × Fin n ≃ (Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) := (e.prodCongr e).symm with hE
    set R := MeasurableEquiv.piCongrLeft (fun _ : (Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) => ℂ) E
    have hGl : Measurable (OmegaPQAux.Gl ε) :=
      (LinearMap.continuous_of_finiteDimensional (OmegaPQAux.Gl ε)).measurable
    have hPm : Measurable (OmegaPQAux.pairMap ε) := by
      rw [OmegaPQAux.pairMap_eq]
      exact (OmegaPQAux.mp_Amap ε).measurable.comp (hGl.comp (OmegaPQAux.mp_Fmap ε).measurable)
    have hcomp : (fun ab : Formalism.BasicNotions.lieU P Q × Formalism.BasicNotions.lieU P Q =>
        Formalism.BasicNotions.entries ((ab.1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) +
          Complex.I • (ab.2 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))) ∘
          Prod.map (gToLie e he1 he2) (gToLie e he1 he2) = R ∘ OmegaPQAux.pairMap ε := by
      funext st ij
      obtain ⟨i, j⟩ := ij
      have hij : ((i, j) : (Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q)) = E (e i, e j) := by simp [hE]
      conv_rhs => rw [hij]
      simp only [Function.comp_apply, R, MeasurableEquiv.coe_piCongrLeft,
        Equiv.piCongrLeft_apply_apply]
      simp [Formalism.BasicNotions.entries, gToLie, gToLieMat, OmegaPQAux.pairMap, Matrix.reindex_apply]
    have hval : ∀ i j, Measurable (fun X : Formalism.BasicNotions.lieU P Q =>
        (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) i j) := fun i j =>
      (continuous_subtype_val.matrix_elem i j).measurable
    have hFm : Measurable (fun ab : Formalism.BasicNotions.lieU P Q × Formalism.BasicNotions.lieU P Q =>
        Formalism.BasicNotions.entries ((ab.1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) +
          Complex.I • (ab.2 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))) := by
      refine measurable_pi_lambda _ fun ij => ?_
      have h1 : Measurable (fun ab : Formalism.BasicNotions.lieU P Q × Formalism.BasicNotions.lieU P Q =>
          (ab.1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) ij.1 ij.2) :=
        (hval ij.1 ij.2).comp measurable_fst
      have h2 : Measurable (fun ab : Formalism.BasicNotions.lieU P Q × Formalism.BasicNotions.lieU P Q =>
          (ab.2 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) ij.1 ij.2) :=
        (hval ij.1 ij.2).comp measurable_snd
      exact h1.add (measurable_const.mul h2)
    rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul,
      Measure.map_prod_map _ _ hG hG, Measure.map_map hFm (hG.prodMap hG), hcomp,
      ← Measure.map_map R.measurable hPm, ← Measure.volume_eq_prod, OmegaPQAux.map_pairMap, Measure.map_smul,
      (volume_measurePreserving_piCongrLeft (fun _ : (Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) => ℂ) E).map_eq,
      smul_smul, hc, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← mul_pow]
    norm_num

end ReciprocityTheory.ChartRestriction.DS
