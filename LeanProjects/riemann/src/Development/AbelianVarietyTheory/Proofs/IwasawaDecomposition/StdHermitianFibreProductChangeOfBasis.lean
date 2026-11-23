import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreMeasuresTransportUnitarySimilitudeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousDistribHaarCharUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNiceLocalFieldProductRingInfiniteAdelesComplet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProductFormulaHaarModulusCmFieldElementStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductMeasureSmulFactorsEqSmulStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRestrictedProductTupleMeasureMapLeftRightActioStatement

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.BasisX

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sigR_inclR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (e : E) :
    sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem hform_eq {A : Type} [CommRing A] (τ : A →+* A) {M : ℕ} (J : Matrix (Fin M) (Fin M) A)
    (x y : Fin M → A) : Formalism.UG.hform τ J x y = (τ ∘ x) ⬝ᵥ J.mulVec y := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec {A : Type} [CommRing A] (τ : A →+* A) {M : ℕ} (J P : Matrix (Fin M) (Fin M) A)
    (x y : Fin M → A) :
    Formalism.UG.hform τ J (P.mulVec x) (P.mulVec y) = Formalism.UG.hform τ (Formalism.UG.cT τ P * J * P) x y := by
  rw [hform_eq, hform_eq]
  have h : (τ ∘ P.mulVec x) = (P.map τ).mulVec (τ ∘ x) := by
    funext i
    exact RingHom.map_mulVec τ P x i
  rw [h, Formalism.UG.cT, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec (τ ∘ x), Matrix.vecMul_transpose]

theorem qR_mulVec (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J P : Matrix (Fin M) (Fin M) E) (z : Fin M → R ⊗[F] E) :
    qR R σ J ((P.map (inclR R)).mulVec z) = qR R σ (Formalism.UG.cT (σ : E →+* E) P * J * P) z := by
  have h : JR R (Formalism.UG.cT (σ : E →+* E) P * J * P) =
      Formalism.UG.cT (sigR R σ) (P.map (inclR R)) * JR R J * P.map (inclR R) := by
    unfold JR
    rw [Matrix.map_mul, Matrix.map_mul]
    have hc : (Formalism.UG.cT (σ : E →+* E) P).map (inclR (F := F) R) =
        Formalism.UG.cT (sigR R σ) (P.map (inclR R)) := by
      ext i j
      exact (sigR_inclR R σ _).symm
    rw [hc]
  unfold qR hR
  rw [hform_mulVec, h]

end Alg

section Proj

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem prInf_inclR (e : E) : prInf (inclR (AF F) e) = inclR (Ainf F) e := by
  simp [prInf, inclR]

theorem prV_inclR (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    prV v (inclR (AF F) e) = inclR (Fv F v) e := by
  simp [prV, inclR]

end Proj

theorem fibAt_basis (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
    (hR : Nice R) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E)
    (lam : Measure (R ⊗[F] E)) (ν : Measure R) (β : R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E))
    (hl : lam.IsAddHaarMeasure) (hν : ν.IsAddHaarMeasure)
    (h : FibAt R σ (Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin M) (Fin M) E) * J *
      (P : Matrix (Fin M) (Fin M) E)) (tupMeas lam 1 M) ν β m) :
    FibAt R σ J (tupMeas lam 1 M) ν β
      (modu (R ⊗[F] E) (inclR R (P : Matrix (Fin M) (Fin M) E).det) •
        m.map (lrAct ((P : Matrix (Fin M) (Fin M) E).map (inclR R)) 1)) := by
  have hdet : ((P : Matrix (Fin M) (Fin M) E).map (inclR (F := F) R)).det =
      inclR R (P : Matrix (Fin M) (Fin M) E).det := (RingHom.map_det _ _).symm
  have hu : IsUnit ((P : Matrix (Fin M) (Fin M) E).map (inclR (F := F) R)).det := by
    rw [hdet]
    exact ((Matrix.isUnits_det_units P)).map _
  have := GlobalTheory.T.fibreMeasures_transport_unitary_similitude F E σ R hR M _ J lam ν β 1 m _ hl hν hu isUnit_one
    (fun z => by rw [one_mul, qR_mulVec]) h
  rw [one_mul, (modu_basic R).2.2.1, inv_one, mul_one, hdet] at this
  exact this

theorem isStdX_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J J' : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E) (β : F) (ν' : Measure (Fin 1 → Fin M → AF F ⊗[F] E)), J' = Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin M) (Fin M) E) * J * (P : Matrix (Fin M) (Fin M) E) → IsStdX s σ J' β ν' → IsStdX s σ J β (ν'.map (lrAct ((P : Matrix (Fin M) (Fin M) E).map (inclR (AF F))) 1)) := by
  intro F E _ _ _ _ _ σ hσ d b s M J J' P β ν' hJ ⟨mi, mv, hi, hv, hp⟩
  subst hJ
  obtain ⟨hni, hnv⟩ := nice_ainf_fv F
  have hdet : (P : Matrix (Fin M) (Fin M) E).det ≠ 0 := (Matrix.isUnits_det_units P).ne_zero
  obtain ⟨hfin, hone⟩ := GlobalTheory.T.product_formula_haarModulus_cmField_element F E σ hσ _ hdet
  refine ⟨_, _, fibAt_basis F E σ (Ainf F) hni M J P _ _ _ _ s.haar_lamI s.haar_nuI hi,
    fun v => fibAt_basis F E σ (Fv F v) (hnv v) M J P _ _ _ _ (s.haar_lamV v) (s.haar_nuV v) (hv v), ?_⟩
  have h1 := GlobalTheory.T.isRestrictedProductTupleMeasure_map_leftRightAction F E d b 1 M ν' mi mv
    (Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F)) P) 1 hp
  have hg : (Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F)) P).val =
      (P : Matrix (Fin M) (Fin M) E).map (inclR (AF F)) := rfl
  have hI : ((P : Matrix (Fin M) (Fin M) E).map (inclR (F := F) (AF F))).map prInf =
      (P : Matrix (Fin M) (Fin M) E).map (inclR (Ainf F)) := by
    ext i j
    exact prInf_inclR _
  have hV : ∀ v, ((P : Matrix (Fin M) (Fin M) E).map (inclR (F := F) (AF F))).map (prV v) =
      (P : Matrix (Fin M) (Fin M) E).map (inclR (Fv F v)) := by
    intro v
    ext i j
    exact prV_inclR v _
  have h1I : (1 : Matrix (Fin 1) (Fin 1) (AF F ⊗[F] E)).map prInf = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have h1V : ∀ v, (1 : Matrix (Fin 1) (Fin 1) (AF F ⊗[F] E)).map (prV v) = 1 := fun v =>
    Matrix.map_one _ (map_zero _) (map_one _)
  simp only [hg, Units.val_one, hI, hV, h1I, h1V] at h1
  have h2 := GlobalTheory.T.restrictedProduct_measure_smul_factors_eq_smul F E d b 1 M _ _ _
    (modu (Ainf F ⊗[F] E) (inclR (Ainf F) (P : Matrix (Fin M) (Fin M) E).det)) _ h1 hfin
  rw [hone, one_smul] at h2
  exact h2

end GlobalTheory.GaugeEx.BasisX
