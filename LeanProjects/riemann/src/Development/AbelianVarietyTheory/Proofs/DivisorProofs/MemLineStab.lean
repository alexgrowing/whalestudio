import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IwasawaKAvgInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def lineStab (σ : E →ₐ[F] E) {n : ℕ} (X : Spc F E n) (x : Fin n → E) : Subgroup (UAtSub σ X (evI F)) where
  carrier := {g | ∃ t : (AE F E)ˣ, mat g.1 *ᵥ incV F x = t.1 • incV F x}
  one_mem' := ⟨1, by simp [GlobalTheory.StabHaar.mat_one]⟩
  mul_mem' := by
    rintro g h ⟨t, ht⟩ ⟨u, hu⟩
    refine ⟨t * u, ?_⟩
    show mat (g.1 * h.1) *ᵥ incV F x = _
    rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_smul, ht, smul_smul, Units.val_mul, mul_comm]
  inv_mem' := by
    rintro g ⟨t, ht⟩
    refine ⟨t⁻¹, ?_⟩
    have h2 : mat g.1⁻¹ *ᵥ (mat g.1 *ᵥ incV F x) = incV F x := by
      rw [Matrix.mulVec_mulVec, ← GlobalTheory.StabHaar.mat_mul, inv_mul_cancel, GlobalTheory.StabHaar.mat_one, Matrix.one_mulVec]
    rw [ht, Matrix.mulVec_smul] at h2
    show mat g.1⁻¹ *ᵥ incV F x = _
    conv_rhs => rw [← h2]
    rw [smul_smul, Units.inv_mul, one_smul]

end GlobalTheory.IwasawaKAvgInt
