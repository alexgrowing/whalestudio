import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviModulus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def hmat (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x u : Fin n → AE F E) (c : AE F E) :
    Matrix (Fin n) (Fin n) (AE F E) :=
  1 + Matrix.vecMulVec (u + c • x) (incM F J *ᵥ fun i => cA σ (x i)) -
    Matrix.vecMulVec x (incM F J *ᵥ fun i => cA σ (u i))

variable (σ : E →ₐ[F] E)

def imA : AddSubgroup (AE F E) where
  carrier := {z | cA σ z = -z}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add] at *
    rw [ha, hb, neg_add]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, map_neg] at *
    rw [ha]

theorem cA_cA (hσ : ∀ a, σ (σ a) = a) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
    show Algebra.TensorProduct.map _ _ (Algebra.TensorProduct.map _ _ (a ⊗ₜ[F] x)) = a ⊗ₜ[F] x
    simp [hσ]

theorem mem_imA {z : AE F E} : z ∈ imA σ ↔ cA σ z = -z := Iff.rfl

variable (F E) in

theorem topAE : IsTopologicalRing (AE F E) ∧ LocallyCompactSpace (AE F E) ∧ SecondCountableTopology (AE F E) ∧
    T2Space (AE F E) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  exact ⟨inferInstance, e.isClosedEmbedding.locallyCompactSpace, e.secondCountableTopology, e.isEmbedding.t2Space⟩

theorem continuous_cA : Continuous (cA σ) := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI := (topAE F E).1
  exact IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap

theorem isClosed_imA : IsClosed (imA σ : Set (AE F E)) := by
  obtain ⟨h1, -, -, h4⟩ := topAE F E
  haveI := h1
  exact isClosed_eq (continuous_cA σ) continuous_neg

theorem topUA {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    IsTopologicalGroup (UA σ J) ∧ LocallyCompactSpace (UA σ J) ∧ SecondCountableTopology (UA σ J) ∧
      T2Space (UA σ J) := by
  obtain ⟨h1, h2, h3, h4⟩ := topAE F E
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AE F E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (Fin n) (AE F E)) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin n) (AE F E)) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : T2Space (GL (Fin n) (AE F E)) := Units.isEmbedding_embedProduct.t2Space
  have hs : Continuous (cA σ) := continuous_cA σ
  have hc : IsClosed (UG (cA σ) (incM F J) : Set (GL (Fin n) (AE F E))) := by
    have hv : Continuous fun g : GL (Fin n) (AE F E) => (g : Matrix (Fin n) (Fin n) (AE F E)) := Units.continuous_val
    exact isClosed_eq ((hv.matrix_transpose.matrix_mul continuous_const).matrix_mul (hv.matrix_map hs))
      continuous_const
  exact ⟨inferInstance, hc.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    hc.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology,
    inferInstanceAs (T2Space (UG (cA σ) (incM F J)))⟩

def conjOn {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G] (N : Subgroup G) (g : G)
    (h₁ : ∀ u ∈ N, g * u * g⁻¹ ∈ N) (h₂ : ∀ u ∈ N, g⁻¹ * u * g ∈ N) : N ≃ₜ* N where
  toFun u := ⟨g * u * g⁻¹, h₁ u u.2⟩
  invFun u := ⟨g⁻¹ * u * g, h₂ u u.2⟩
  left_inv u := Subtype.ext (by simp [mul_assoc])
  right_inv u := Subtype.ext (by simp [mul_assoc])
  map_mul' u v := Subtype.ext (by simp [mul_assoc])
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem conjOn_apply {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G] (N : Subgroup G) (g : G)
    (h₁ : ∀ u ∈ N, g * u * g⁻¹ ∈ N) (h₂ : ∀ u ∈ N, g⁻¹ * u * g ∈ N) (u : N) :
    ((conjOn N g h₁ h₂ u : N) : G) = g * u * g⁻¹ := rfl

end GlobalTheory.LeviModulus

end
