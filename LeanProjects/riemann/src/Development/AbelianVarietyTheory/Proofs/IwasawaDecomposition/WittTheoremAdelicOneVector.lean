import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableEmbeddingAdelicTupleLocalComponentsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNiceLocalFieldProductRingInfiniteAdelesCompletStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianQuadraticUnitaryLocalComponentsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralWittTheoremAlmostAllPlacesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmExtensionLocalFieldProductRingExistsSmulEqStatement

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.AdelicWitt

theorem qR_ratTup {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E]
    (b : Module.Basis (Fin 2) F E) (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (β : F)
    (h : hE σ J (x 0) (x 0) = algebraMap F E β) :
    qR R σ J (ratTup (F := F) R x 0) = algebraMap F R β := by
  have h1 : hR R σ J (ratTup (F := F) R x 0) (ratTup (F := F) R x 0) =
      inclR (F := F) R (hE σ J (x 0) (x 0)) := by
    simp only [hR, hE, Formalism.UG.hform, map_sum, map_mul, ratTup, JR, Matrix.map_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 2
  have h2 : inclR (F := F) R (algebraMap F E β) = algebraMap R (R ⊗[F] E) (algebraMap F R β) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes β
  rw [qR, h1, h, h2, Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R b),
    Fintype.card_fin, ← map_nsmul, ← map_mul]
  congr 1
  rw [nsmul_eq_mul]; push_cast; field_simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in
theorem prInf_sigR (σ : E →ₐ[F] E) (z : AF F ⊗[F] E) :
    prInf (sigR (AF F) σ z) = sigR (Ainf F) σ (prInf z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add a c ha hc => simp only [map_add, ha, hc]

omit [NumberField E] in
theorem prV_sigR (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    prV v (sigR (AF F) σ z) = sigR (Fv F v) σ (prV v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add a c ha hc => simp only [map_add, ha, hc]

omit [NumberField E] in
theorem prInf_inclR (e : E) : prInf (inclR (F := F) (AF F) e) = inclR (F := F) (Ainf F) e := by
  simp [prInf, inclR]

omit [NumberField E] in
theorem prV_inclR (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    prV v (inclR (F := F) (AF F) e) = inclR (F := F) (Fv F v) e := by
  simp [prV, inclR]

theorem ext_comp {d : ℕ} (b : Module.Basis (Fin d) F E) {n M : ℕ} (X Y : Fin n → Fin M → AF F ⊗[F] E)
    (hi : ∀ a i, prInf (X a i) = prInf (Y a i))
    (hv : ∀ (v : HeightOneSpectrum (𝓞 F)) a i, prV v (X a i) = prV v (Y a i)) : X = Y := by
  apply (GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents F E d b n M).1.injective
  refine Prod.ext ?_ ?_
  · funext a i; exact hi a i
  · funext v a i; exact hv v a i

theorem mat_ext {d : ℕ} (b : Module.Basis (Fin d) F E) {M : ℕ}
    (X Y : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))
    (hi : X.map prInf = Y.map prInf)
    (hv : ∀ v : HeightOneSpectrum (𝓞 F), X.map (prV v) = Y.map (prV v)) : X = Y :=
  ext_comp b X Y (fun a i => congrFun (congrFun hi a) i) (fun v a i => congrFun (congrFun (hv v) a) i)

theorem exists_mat {d : ℕ} (b : Module.Basis (Fin d) F E) {M : ℕ}
    (Xi : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E))
    (Xv : ∀ v : HeightOneSpectrum (𝓞 F), Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E))
    (h : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j, Xv v i j ∈ intV b v) :
    ∃ X : Matrix (Fin M) (Fin M) (AF F ⊗[F] E), X.map prInf = Xi ∧ ∀ v, X.map (prV v) = Xv v := by
  have := ((Set.ext_iff.1 (GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents F E d b M M).2.1) (Xi, Xv)).2 h
  obtain ⟨X, hX⟩ := this
  exact ⟨X, congrArg Prod.fst hX, fun v => congrFun (congrArg Prod.snd hX) v⟩

theorem map_unit {A B : Type} [CommRing A] [CommRing B] {M : ℕ} (φ : A →+* B) (s : A →+* A)
    (t : B →+* B) (h : ∀ z, φ (s z) = t (φ z)) (X J : Matrix (Fin M) (Fin M) A) :
    (Formalism.UG.cT s X * J * X).map φ = Formalism.UG.cT t (X.map φ) * J.map φ * X.map φ := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 2
  ext i j
  exact h _

theorem exists_HA {d : ℕ} (b : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (gi : HA (Ainf F) σ J)
    (gv : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J)
    (h : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j,
      (HA.mat (Fv F v) σ J (gv v)).val i j ∈ intV b v ∧
        (HA.mat (Fv F v) σ J (gv v)⁻¹).val i j ∈ intV b v) :
    ∃ g : HA (AF F) σ J, (HA.mat (AF F) σ J g).val.map prInf = (HA.mat (Ainf F) σ J gi).val ∧
      ∀ v, (HA.mat (AF F) σ J g).val.map (prV v) = (HA.mat (Fv F v) σ J (gv v)).val := by
  obtain ⟨X, hXi, hXv⟩ := exists_mat b (HA.mat (Ainf F) σ J gi).val
    (fun v => (HA.mat (Fv F v) σ J (gv v)).val) (h.mono fun v hv i j => (hv i j).1)
  obtain ⟨Y, hYi, hYv⟩ := exists_mat b (HA.mat (Ainf F) σ J gi).inv
    (fun v => (HA.mat (Fv F v) σ J (gv v)).inv) (h.mono fun v hv i j => (hv i j).2)
  have hXY : X * Y = 1 := by
    refine mat_ext b _ _ ?_ fun v => ?_
    · rw [Matrix.map_mul, hXi, hYi, Units.val_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [Matrix.map_mul, hXv, hYv, Units.val_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hYX : Y * X = 1 := by
    refine mat_ext b _ _ ?_ fun v => ?_
    · rw [Matrix.map_mul, hXi, hYi, Units.inv_val, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [Matrix.map_mul, hXv, hYv, Units.inv_val, Matrix.map_one _ (map_zero _) (map_one _)]
  have hJi : (JR (F := F) (AF F) J).map prInf = JR (F := F) (Ainf F) J := by
    ext i j; exact prInf_inclR _
  have hJv : ∀ v, (JR (F := F) (AF F) J).map (prV v) = JR (F := F) (Fv F v) J := by
    intro v; ext i j; exact prV_inclR v _
  have hU : Formalism.UG.cT (sigR (AF F) σ) X * JR (F := F) (AF F) J * X = JR (F := F) (AF F) J := by
    refine mat_ext b _ _ ?_ fun v => ?_
    · rw [map_unit _ _ _ (prInf_sigR σ), hXi, hJi]
      exact (show HR (Ainf F) σ J from gi).2
    · rw [map_unit _ _ _ (prV_sigR σ v), hXv, hJv]
      exact (show HR (Fv F v) σ J from gv v).2
  exact ⟨(show HR (AF F) σ J from ⟨⟨X, Y, hXY, hYX⟩, hU⟩), hXi, hXv⟩

theorem witt_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (β : F), IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β → ∀ y : (Fin 1 → Fin M → AF F ⊗[F] E), qR (AF F) σ J (y 0) = algebraMap F (AF F) β → ∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) x = y := by
  intro F E _ _ _ _ _ σ hCM M J x β hJ hβ hx y hy
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hCM.2.2.1
  obtain ⟨hyi, hyv⟩ := ((GlobalTheory.T.hermitianQuadratic_unitary_local_components F E σ M J).1 (y 0) β).1 hy
  have hu : IsUnit β := hβ.isUnit
  obtain ⟨gi, hgi⟩ := GlobalTheory.T.cmExtension_localFieldProductRing_exists_smul_eq F E σ hCM (Ainf F) (GlobalTheory.T.isNiceLocalFieldProductRing_infiniteAdeles_completions F).1 M J hJ
    (algebraMap F _ β) (ratTup (F := F) (Ainf F) x) (projInf y) (hu.map _)
    (qR_ratTup b _ σ J x β hx) hyi
  have hlat : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, projV v (projFin y) ∈ latV b v := by
    have h := (GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents F E 2 b 1 M).2.1 ▸ Set.mem_range_self (f := fun X : (Fin 1 → Fin M → AF F ⊗[F] E) =>
      (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) y
    exact h
  have hae := GlobalTheory.T.integral_witt_theorem_almost_all_places F E σ hCM 2 b M J x β hJ hβ hx
  let P : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J → Prop := fun v g => ∀ i j,
      (HA.mat (Fv F v) σ J g).val i j ∈ intV b v ∧ (HA.mat (Fv F v) σ J g⁻¹).val i j ∈ intV b v
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ g : HA (Fv F v) σ J,
      g • ratTup (F := F) (Fv F v) x = projV v (projFin y) ∧
      ((∃ g' : HA (Fv F v) σ J, g' • ratTup (F := F) (Fv F v) x = projV v (projFin y) ∧ P v g') →
        P v g) := by
    intro v
    by_cases h : ∃ g' : HA (Fv F v) σ J,
        g' • ratTup (F := F) (Fv F v) x = projV v (projFin y) ∧ P v g'
    · obtain ⟨g, h1, h2⟩ := h
      exact ⟨g, h1, fun _ => h2⟩
    · obtain ⟨g, hg⟩ := GlobalTheory.T.cmExtension_localFieldProductRing_exists_smul_eq F E σ hCM (Fv F v) ((GlobalTheory.T.isNiceLocalFieldProductRing_infiniteAdeles_completions F).2 v) M J hJ
        (algebraMap F _ β) (ratTup (F := F) (Fv F v) x) (projV v (projFin y)) (hu.map _)
        (qR_ratTup b _ σ J x β hx) (hyv v)
      exact ⟨g, hg, fun h' => absurd h' h⟩
  choose gv hgv hP using hloc
  obtain ⟨g, hi, hv⟩ := exists_HA b σ J gi gv (by
    filter_upwards [hlat, hae] with v h1 h2
    exact hP v (h2 _ h1 (hyv v)))
  refine ⟨g, ext_comp b _ _ (fun a i => ?_) (fun v a i => ?_)⟩
  · have h1 := congrFun (congrFun hgi a) i
    rw [projInf_apply] at h1
    rw [← h1]
    show prInf ((HA.mat (AF F) σ J g).val.mulVec (ratTup (F := F) (AF F) x a) i) =
      (HA.mat (Ainf F) σ J gi).val.mulVec (ratTup (F := F) (Ainf F) x a) i
    rw [RingHom.map_mulVec, hi]
    exact congrArg (fun w => (HA.mat (Ainf F) σ J gi).val.mulVec w i)
      (funext fun k => prInf_inclR (x a k))
  · have h1 := congrFun (congrFun (hgv v) a) i
    rw [projV_apply] at h1
    rw [← h1]
    show prV v ((HA.mat (AF F) σ J g).val.mulVec (ratTup (F := F) (AF F) x a) i) =
      (HA.mat (Fv F v) σ J (gv v)).val.mulVec (ratTup (F := F) (Fv F v) x a) i
    rw [RingHom.map_mulVec, hv]
    exact congrArg (fun w => (HA.mat (Fv F v) σ J (gv v)).val.mulVec w i)
      (funext fun k => prV_inclR v (x a k))

end GlobalTheory.AdelicWitt
