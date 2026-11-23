import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

noncomputable section

open scoped Kronecker

namespace GlobalTheory.ModuLR

section Conj

theorem addEquivAddHaarChar_transport {A B : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [MeasurableSpace A] [BorelSpace A] [AddCommGroup B] [TopologicalSpace B]
    [IsTopologicalAddGroup B] [LocallyCompactSpace B] [MeasurableSpace B] [BorelSpace B]
    (e : A ≃ₜ+ B) (φ : A ≃ₜ+ A) :
    addEquivAddHaarChar ((e.symm.trans φ).trans e) = addEquivAddHaarChar φ := by
  set ν : Measure A := Measure.addHaar
  set μ : Measure B := ν.map e
  haveI : μ.IsAddHaarMeasure := e.isAddHaarMeasure_map ν
  haveI : μ.Regular := Measure.Regular.map e.toHomeomorph
  set ψ : B ≃ₜ+ B := (e.symm.trans φ).trans e
  have he : Measurable e := e.continuous.measurable
  have hφ : Measurable φ := φ.continuous.measurable
  have hψ : Measurable ψ := ψ.continuous.measurable
  have h1 := addEquivAddHaarChar_smul_map ν φ
  have h2 := addEquivAddHaarChar_smul_map μ ψ
  have hm : μ.map ψ = (ν.map φ).map e := by
    rw [Measure.map_map hψ he, Measure.map_map he hφ]
    congr 1
    funext x
    simp [ψ]
  have h3 : addEquivAddHaarChar φ • μ.map ψ = μ := by rw [hm, ← Measure.map_smul, h1]
  haveI : (μ.map ψ).IsAddHaarMeasure := ψ.isAddHaarMeasure_map μ
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (0 : B)
  have hpos : (μ.map ψ) K ≠ 0 := (Measure.measure_pos_of_mem_nhds (μ := μ.map ψ) hKn).ne'
  have htop : (μ.map ψ) K ≠ ⊤ := (hK.measure_lt_top).ne
  have h4 : (addEquivAddHaarChar ψ : ℝ≥0∞) * (μ.map ψ) K = (addEquivAddHaarChar φ : ℝ≥0∞) * (μ.map ψ) K := by
    have a2 := congrArg (fun m : Measure B => m K) h2
    have a3 := congrArg (fun m : Measure B => m K) h3
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at a2 a3
    rw [a2, a3]
  exact_mod_cast (ENNReal.mul_left_inj hpos htop).1 h4

end Conj

section Det

variable {S : Type} [CommRing S] {m n : ℕ}

def lrLin (g : Matrix (Fin m) (Fin m) S) (a : Matrix (Fin n) (Fin n) S) :
    Matrix (Fin m) (Fin n) S →ₗ[S] Matrix (Fin m) (Fin n) S where
  toFun u := g * u * a
  map_add' u v := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c u := by simp [Matrix.mul_smul, Matrix.smul_mul]

theorem det_lrLin (g : Matrix (Fin m) (Fin m) S) (a : Matrix (Fin n) (Fin n) S) :
    LinearMap.det (lrLin g a) = g.det ^ n * a.det ^ m := by
  let e : Matrix (Fin m) (Fin n) S ≃ₗ[S] (Fin m × Fin n → S) := (LinearEquiv.curry S S (Fin m) (Fin n)).symm
  have key : (e : Matrix (Fin m) (Fin n) S →ₗ[S] (Fin m × Fin n → S)) ∘ₗ lrLin g a ∘ₗ
      (e.symm : (Fin m × Fin n → S) →ₗ[S] Matrix (Fin m) (Fin n) S) = Matrix.toLin' (g ⊗ₖ aᵀ) := by
    refine LinearMap.ext fun x => funext fun p => ?_
    obtain ⟨i, j⟩ := p
    change (g * Matrix.of (Function.curry x) * a) i j = _
    simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.transpose_apply, Matrix.mul_apply, Finset.sum_mul, Function.curry_apply, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [← LinearMap.det_conj (lrLin g a) e, key, LinearMap.det_toLin', Matrix.det_kronecker, Matrix.det_transpose]
  simp

end Det

end GlobalTheory.ModuLR

namespace GlobalTheory.ModuLR

section Restr

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev tensBasis : Module.Basis (Fin (Module.finrank F E)) (AF F) (AF F ⊗[F] E) :=
  Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)

def matCoord (m n : ℕ) :
    Matrix (Fin m) (Fin n) (AF F ⊗[F] E) ≃ₗ[AF F] (Fin m × Fin n × Fin (Module.finrank F E) → AF F) where
  toFun u p := (tensBasis F E).equivFun (u p.1 p.2.1) p.2.2
  invFun x := Matrix.of fun i j => (tensBasis F E).equivFun.symm fun k => x (i, j, k)
  left_inv u := by
    ext i j
    simp only [Matrix.of_apply]
    exact (tensBasis F E).equivFun.symm_apply_apply (u i j)
  right_inv x := by
    funext p
    obtain ⟨i, j, k⟩ := p
    show (tensBasis F E).equivFun ((tensBasis F E).equivFun.symm fun k => x (i, j, k)) k = x (i, j, k)
    rw [LinearEquiv.apply_symm_apply]
  map_add' u v := by funext p; simp
  map_smul' c u := by funext p; simp

theorem continuous_matCoord (m n : ℕ) : Continuous (matCoord F E m n) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have hb : Continuous (tensBasis F E).equivFun :=
    IsModuleTopology.continuous_of_linearMap (tensBasis F E).equivFun.toLinearMap
  exact continuous_pi fun p => (continuous_apply p.2.2).comp
    (hb.comp ((continuous_apply p.2.1).comp (continuous_apply p.1)))

theorem continuous_matCoord_symm (m n : ℕ) : Continuous (matCoord F E m n).symm := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have hb : Continuous (tensBasis F E).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap (tensBasis F E).equivFun.symm.toLinearMap
  exact continuous_pi fun i => continuous_pi fun j =>
    hb.comp (continuous_pi fun k => continuous_apply (i, j, k))

def matCoordCE (m n : ℕ) :
    Matrix (Fin m) (Fin n) (AF F ⊗[F] E) ≃ₜ+ (Fin m × Fin n × Fin (Module.finrank F E) → AF F) :=
  { (matCoord F E m n).toAddEquiv with
    continuous_toFun := continuous_matCoord F E m n
    continuous_invFun := continuous_matCoord_symm F E m n }

end Restr

end GlobalTheory.ModuLR

namespace GlobalTheory.ModuLR

theorem exists_matrix_restrictScalars_lrCE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (m n : ℕ) [LocallyCompactSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [SecondCountableTopology (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [MeasurableSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [BorelSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] (g : GL (Fin m) (AF F ⊗[F] E)) (a : GL (Fin n) (AF F ⊗[F] E)), ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (Λ : Matrix κ κ (AF F)) (hΛ : IsUnit Λ.det), Λ.det = Algebra.norm (AF F) ((Matrix.GeneralLinearGroup.det g ^ n * Matrix.GeneralLinearGroup.det a ^ m : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) ∧ addEquivAddHaarChar (lrCE g a) = addEquivAddHaarChar (mulVecCE Λ hΛ) := by
  intro F E _ _ _ _ _ m n _ _ _ _ g a
  haveI : IsScalarTower (AF F) (AF F ⊗[F] E) (Matrix (Fin m) (Fin n) (AF F ⊗[F] E)) := inferInstance
  haveI : Module.Free (AF F) (AF F ⊗[F] E) := Module.Free.of_basis (tensBasis F E)
  haveI : Module.Finite (AF F) (AF F ⊗[F] E) := Module.Finite.of_basis (tensBasis F E)
  set Φ := matCoord F E m n
  set f : Matrix (Fin m) (Fin n) (AF F ⊗[F] E) →ₗ[AF F ⊗[F] E] Matrix (Fin m) (Fin n) (AF F ⊗[F] E) :=
    lrLin (g : Matrix (Fin m) (Fin m) (AF F ⊗[F] E)) (a : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))
  set Λ := LinearMap.toMatrix' (Φ.toLinearMap ∘ₗ f.restrictScalars (AF F) ∘ₗ Φ.symm.toLinearMap)
  have hdet : Λ.det = Algebra.norm (AF F) ((Matrix.GeneralLinearGroup.det g ^ n * Matrix.GeneralLinearGroup.det a ^ m :
      (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) := by
    rw [LinearMap.det_toMatrix', LinearMap.det_conj, LinearMap.det_restrictScalars, det_lrLin]
    simp [Matrix.GeneralLinearGroup.val_det_apply]
  have hΛ : IsUnit Λ.det := hdet ▸ (Units.isUnit _).map (Algebra.norm (AF F))
  refine ⟨_, inferInstance, inferInstance, Λ, hΛ, hdet, ?_⟩
  have hc : mulVecCE Λ hΛ = ((matCoordCE F E m n).symm.trans (lrCE g a)).trans (matCoordCE F E m n) := by
    ext x
    rw [mulVecCE_apply, LinearMap.toMatrix'_mulVec]
    rfl
  rw [hc, addEquivAddHaarChar_transport]

end GlobalTheory.ModuLR
