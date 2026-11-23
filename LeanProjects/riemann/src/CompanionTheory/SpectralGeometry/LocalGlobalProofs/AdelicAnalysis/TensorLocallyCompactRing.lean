import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.TopK

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

omit [IsTopologicalRing R] in

theorem isModTop : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩

def coordHomeo {d : ℕ} (b : Module.Basis (Fin d) F E) : (R ⊗[F] E) ≃ₜ (Fin d → R) :=
  haveI : IsModuleTopology R (R ⊗[F] E) := isModTop R
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
  { (Algebra.TensorProduct.basis R b).equivFun.toEquiv with
    continuous_toFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
    continuous_invFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap }

theorem isHomeomorph_coord {d : ℕ} (b : Module.Basis (Fin d) F E) :
    IsHomeomorph fun (y : R ⊗[F] E) (k : Fin d) => (Algebra.TensorProduct.basis R b).repr y k :=
  (coordHomeo R b).isHomeomorph

theorem isTopRing [Module.Finite F E] : IsTopologicalRing (R ⊗[F] E) :=
  haveI : IsModuleTopology R (R ⊗[F] E) := isModTop R
  IsModuleTopology.isTopologicalRing R (R ⊗[F] E)

omit [IsTopologicalRing R] in
theorem continuous_sigR (σ : E →ₐ[F] E) : Continuous (sigR R σ) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := isModTop R
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
  exact IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap

theorem continuous_trace [Module.Finite F E] : Continuous (Algebra.trace R (R ⊗[F] E)) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := isModTop R
  exact IsModuleTopology.continuous_of_linearMap _

end

theorem topTens_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R], IsTopologicalRing (R ⊗[F] E) ∧ LocallyCompactSpace (R ⊗[F] E) ∧ SecondCountableTopology (R ⊗[F] E) ∧ T2Space (R ⊗[F] E) ∧ Continuous (sigR R σ) ∧ Continuous (Algebra.trace R (R ⊗[F] E)) ∧ (∀ (d : ℕ) (b : Module.Basis (Fin d) F E), IsHomeomorph fun (y : R ⊗[F] E) (k : Fin d) => (Algebra.TensorProduct.basis R b).repr y k) ∧ (∀ n M : ℕ, BorelSpace (Fin n → Fin M → R ⊗[F] E)) ∧ (∀ n : ℕ, IsClosed (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E)))) ∧ (∀ (n M : ℕ) (J : Matrix (Fin M) (Fin M) E), Continuous (gramR R σ J : (Fin n → Fin M → R ⊗[F] E) → _)) := by
  intro F E _ _ _ _ _ σ _ R _ _ _ _ _ _ _
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have e := coordHomeo R (Module.finBasis F E)
  haveI h1 : IsTopologicalRing (R ⊗[F] E) := isTopRing R
  haveI h2 : LocallyCompactSpace (R ⊗[F] E) := e.isOpenEmbedding.locallyCompactSpace
  haveI h3 : SecondCountableTopology (R ⊗[F] E) := e.secondCountableTopology
  haveI h4 : T2Space (R ⊗[F] E) := e.isEmbedding.t2Space
  haveI h5 : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hs := continuous_sigR R σ
  refine ⟨h1, h2, h3, h4, hs, continuous_trace R, fun d b => isHomeomorph_coord R b,
    fun n M => inferInstance, fun n => ?_, fun n M J => ?_⟩
  · have : (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
        ⋂ a, ⋂ b, {S | sigR R σ (S b a) = S a b} := by
      ext S
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      rfl
    rw [this]
    refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_eq ?_ ?_
    · exact hs.comp (continuous_id.matrix_elem b a)
    · exact continuous_id.matrix_elem a b
  · refine continuous_pi fun a => continuous_pi fun b => ?_
    unfold gramR hR hform
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    exact ((hs.comp ((continuous_apply i).comp (continuous_apply a))).mul continuous_const).mul
      ((continuous_apply j).comp (continuous_apply b))

end GlobalTheory.CompanionTheory.SW.TopK
