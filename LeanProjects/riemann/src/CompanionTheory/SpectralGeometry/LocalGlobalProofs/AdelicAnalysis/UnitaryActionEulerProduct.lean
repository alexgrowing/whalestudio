import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LinearChangeEulerProductStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PfAct

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def actMat (n : ℕ) {d M : ℕ} (b : Module.Basis (Fin d) F E) (g : Matrix (Fin M) (Fin M) E) :
    Matrix (Fin n × Fin M × Fin d) (Fin n × Fin M × Fin d) F :=
  fun p q => if p.1 = q.1 then Algebra.leftMulMatrix b (g p.2.1 q.2.1) p.2.2 q.2.2 else 0

variable (R : Type) [CommRing R] [Algebra F R]

def coTup {n M d : ℕ} (b : Module.Basis (Fin d) F E) (X : Fin n → Fin M → R ⊗[F] E) :
    Fin n × Fin M × Fin d → R :=
  fun p => (Algebra.TensorProduct.basis R b).repr (X p.1 p.2.1) p.2.2

theorem repr_incl_mul {d : ℕ} (b : Module.Basis (Fin d) F E) (e : E) (y : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (inclR R e * y) k =
      ∑ l, algebraMap F R (Algebra.leftMulMatrix b e k l) *
        (Algebra.TensorProduct.basis R b).repr y l := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [mul_add, map_add, Finsupp.add_apply, hx, hy, Finset.sum_add_distrib]
  | tmul r e' =>
    have h1 : inclR R e * (r ⊗ₜ[F] e') = r ⊗ₜ[F] (e * e') := by
      simp [inclR]
    have h2 := congrFun (Algebra.leftMulMatrix_mulVec_repr b e e') k
    rw [h1]
    simp only [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, smul_eq_mul,
      Finsupp.mapRange_apply]
    rw [← h2]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring

theorem coTup_mulVec {n M d : ℕ} (b : Module.Basis (Fin d) F E) (G : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) :
    coTup R b (fun a => G.map (inclR R) *ᵥ X a) =
      (actMat n b G).map (algebraMap F R) *ᵥ coTup R b X := by
  funext ⟨a, i, k⟩
  have h0 : (G.map (inclR R) *ᵥ X a) i = ∑ j, inclR R (G i j) * X a j := by
    simp [Matrix.mulVec, dotProduct]
  simp only [coTup, h0, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply, repr_incl_mul]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, actMat, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · simp [coTup]
  · intro a' _ h
    simp [Ne.symm h]
  · simp

theorem coTup_act {n M d : ℕ} (b : Module.Basis (Fin d) F E) (g : GL (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) :
    coTup R b (actTup R (bc (inclR R) g) X) =
      (actMat n b (g : Matrix (Fin M) (Fin M) E)).map (algebraMap F R) *ᵥ coTup R b X :=
  coTup_mulVec R b (g : Matrix (Fin M) (Fin M) E) X

def coEquiv {n M d : ℕ} (b : Module.Basis (Fin d) F E) :
    (Fin n → Fin M → R ⊗[F] E) ≃ (Fin n × Fin M × Fin d → R) where
  toFun := coTup R b
  invFun y a i := (Algebra.TensorProduct.basis R b).equivFun.symm fun k => y (a, i, k)
  left_inv X := by
    funext a i
    exact (Algebra.TensorProduct.basis R b).equivFun.symm_apply_apply (X a i)
  right_inv y := by
    funext ⟨a, i, k⟩
    exact congrFun ((Algebra.TensorProduct.basis R b).equivFun.apply_symm_apply
      fun k => y (a, i, k)) k

theorem det_actMat_ne_zero (n : ℕ) {M d : ℕ} (b : Module.Basis (Fin d) F E) (g : GL (Fin M) E) :
    (actMat n b (g : Matrix (Fin M) (Fin M) E)).det ≠ 0 := by
  have hs : Function.Surjective (actMat n b (g : Matrix (Fin M) (Fin M) E)).mulVec := by
    intro y
    refine ⟨coTup F b (actTup F (bc (inclR F) g⁻¹) ((coEquiv F b).symm y)), ?_⟩
    have h := coTup_act F b g (actTup F (bc (inclR F) g⁻¹) ((coEquiv F b).symm y))
    have h1 : (actMat n b (g : Matrix (Fin M) (Fin M) E)).map (algebraMap F F) =
        actMat n b (g : Matrix (Fin M) (Fin M) E) := by
      ext p q
      simp
    rw [h1] at h
    rw [← h]
    have h2 : actTup F (bc (inclR F) g) (actTup F (bc (inclR F) g⁻¹) ((coEquiv F b).symm y)) =
        (coEquiv F b).symm y := by
      funext a
      have : (bc (inclR (F := F) (E := E) F) g).1 * (bc (inclR (F := F) (E := E) F) g⁻¹).1 = 1 := by
        rw [← Units.val_mul, ← map_mul]
        simp
      simp only [actTup, Matrix.mulVec_mulVec, this, Matrix.one_mulVec]
    rw [h2]
    exact (coEquiv F b).apply_symm_apply y
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_surjective_iff_isUnit.mp hs)).ne_zero

section Top

variable [TopologicalSpace R] [IsTopologicalRing R]

def coHomeo {n M d : ℕ} (b : Module.Basis (Fin d) F E) :
    (Fin n → Fin M → R ⊗[F] E) ≃ₜ (Fin n × Fin M × Fin d → R) where
  toEquiv := coEquiv R b
  continuous_toFun := by
    refine continuous_pi fun p => ?_
    have h := (TopK.coordHomeo R b).continuous
    exact ((continuous_apply p.2.2).comp h).comp
      ((continuous_apply p.2.1).comp (continuous_apply p.1))
  continuous_invFun := by
    refine continuous_pi fun a => continuous_pi fun i => ?_
    exact (TopK.coordHomeo R b).symm.continuous.comp
      (continuous_pi fun k => continuous_apply (a, i, k))

end Top

end Coord

section Meas

variable {F E : Type} [Field F] [Field E] [Algebra F E] [Module.Finite F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]

theorem map_actTup {n M d : ℕ} (b : Module.Basis (Fin d) F E) (g : GL (Fin M) E) (c : ℝ≥0)
    (h : ∀ ν : Measure (Fin n × Fin M × Fin d → R), ν.IsAddHaarMeasure →
      ν.map (fun x => (actMat n b (g : Matrix (Fin M) (Fin M) E)).map (algebraMap F R) *ᵥ x) = c • ν)
    (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (hμ : μ.IsAddHaarMeasure) :
    μ.map (actTup R (bc (inclR R) g)) = c • μ := by
  haveI : IsTopologicalRing (R ⊗[F] E) := TopK.isTopRing R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have e0 := TopK.coordHomeo R (Module.finBasis F E)
  haveI : SecondCountableTopology (R ⊗[F] E) := e0.secondCountableTopology
  let e : (Fin n → Fin M → R ⊗[F] E) ≃ₜ (Fin n × Fin M × Fin d → R) := coHomeo R b
  let f : (Fin n → Fin M → R ⊗[F] E) →+ (Fin n × Fin M × Fin d → R) :=
    { toFun := e
      map_zero' := by
        funext p
        simp [e, coHomeo, coEquiv, coTup]
      map_add' := by
        intro X Y
        funext p
        simp [e, coHomeo, coEquiv, coTup] }
  have hν : (μ.map e).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map μ f e.continuous e.surjective e.isClosedEmbedding.tendsto_cocompact
  set A := (actMat n b (g : Matrix (Fin M) (Fin M) E)).map (algebraMap F R) with hA
  have hAc : Continuous fun x : Fin n × Fin M × Fin d → R => A *ᵥ x :=
    continuous_const.matrix_mulVec continuous_id
  have hact : actTup R (bc (inclR R) g) = e.symm ∘ (fun x => A *ᵥ x) ∘ e := by
    funext X
    apply e.injective
    rw [Function.comp_apply, Function.comp_apply, e.apply_symm_apply]
    exact coTup_act R b g X
  have he : Measurable e := e.continuous.measurable
  have hes : Measurable e.symm := e.symm.continuous.measurable
  have h1 := h _ hν
  rw [hact]
  calc μ.map (e.symm ∘ (fun x => A *ᵥ x) ∘ e)
      = ((μ.map e).map fun x => A *ᵥ x).map e.symm := by
        rw [Measure.map_map hAc.measurable he, Measure.map_map hes (hAc.measurable.comp he)]
    _ = (c • μ.map e).map e.symm := by rw [h1]
    _ = c • μ := by
        rw [Measure.map_smul, Measure.map_map hes he]
        simp

end Meas

theorem product_formula_actTup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M : ℕ) (g : GL (Fin M) E), ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E), μ.IsAddHaarMeasure → μ.map (actTup (Ainf F) (bc (inclR (Ainf F)) g)) = cinf • μ) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (∀ μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E), μ.IsAddHaarMeasure → μ.map (actTup (Fv F v) (bc (inclR (Fv F v)) g)) = c v • μ) := by
  intro F E _ _ _ _ _ σ hσ n M g
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  obtain ⟨cinf, c, hU, hinf, hv⟩ := GlobalTheory.T.addHaar_map_mulVec_eq_smul_at_all_places F _
    (actMat n b (g : Matrix (Fin M) (Fin M) E)) (det_actMat_ne_zero n b g)
  refine ⟨cinf, c, hU, ?_, fun v => ?_⟩
  · obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hσ.1
    haveI := h1
    haveI := h2
    haveI := h3
    haveI := h4
    haveI : BorelSpace (Ainf F) := ⟨rfl⟩
    exact map_actTup (Ainf F) b g cinf hinf
  · obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
    haveI := h1
    haveI := h2
    haveI := h3
    haveI := h4
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    exact map_actTup (Fv F v) b g (c v) (hv v)

end GlobalTheory.CompanionTheory.SW.PfAct
