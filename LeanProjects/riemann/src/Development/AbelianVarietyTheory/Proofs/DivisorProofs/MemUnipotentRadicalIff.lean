import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.UnipSet

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def unipSet (σ : E →ₐ[F] E) {n n₁ : ℕ} (X : Spc F E n) (H : Plane E n n₁) : Subgroup (UA σ X.J) where
  carrier := {u | mat u *ᵥ incV F H.x = incV F H.x ∧
    ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + a • incV F H.x}
  one_mem' := by
    refine ⟨by rw [GlobalTheory.StabHaar.mat_one, Matrix.one_mulVec], fun z => ⟨0, ?_⟩⟩
    rw [GlobalTheory.StabHaar.mat_one, Matrix.one_mulVec, zero_smul, add_zero]
  mul_mem' := by
    rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
    refine ⟨?_, fun z => ?_⟩
    · rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, hv1, hu1]
    · obtain ⟨b, hb⟩ := hv2 z
      obtain ⟨a, ha⟩ := hu2 z
      refine ⟨a + b, ?_⟩
      rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, hb, Matrix.mulVec_add, Matrix.mulVec_smul, ha, hu1,
        add_smul, add_assoc]
  inv_mem' := by
    rintro u ⟨hu1, hu2⟩
    have e : ∀ w, mat u⁻¹ *ᵥ (mat u *ᵥ w) = w := fun w => by
      rw [Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_inv_mul, Matrix.one_mulVec]
    have h1 : mat u⁻¹ *ᵥ incV F H.x = incV F H.x := by
      have := e (incV F H.x); rwa [hu1] at this
    refine ⟨h1, fun z => ?_⟩
    obtain ⟨a, ha⟩ := hu2 z
    refine ⟨-a, ?_⟩
    have := e (incM F H.ι *ᵥ z)
    rw [ha, Matrix.mulVec_add, Matrix.mulVec_smul, h1] at this
    rw [neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq]; exact this

theorem mem_unip_iff (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n n₁ : ℕ) (X : Spc F E n) (H : Plane E n n₁) (u : UA σ X.J) : u ∈ unip σ X H ↔
      (mat u *ᵥ incV F H.x = incV F H.x ∧ ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + a • incV F H.x) := by
  have hc : unip σ X H = unipSet σ X H := by
    apply le_antisymm
    · exact (Subgroup.closure_le _).2 fun v hv => hv
    · intro v hv; exact Subgroup.subset_closure hv
  rw [hc]; rfl

end GlobalTheory.UnipSet
