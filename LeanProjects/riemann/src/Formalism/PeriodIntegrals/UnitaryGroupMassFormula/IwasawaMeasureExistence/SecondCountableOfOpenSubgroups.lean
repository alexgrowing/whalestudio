import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.ParabolicFundamentalDomain

noncomputable section

namespace PI.IwaMeasEx.Sk

open MeasureTheory Topology Filter Matrix
open scoped TensorProduct
open Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma

section Abstract

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

end Abstract

section Gf

variable (I : AutInst)

def kCong (g : ℕ) : Subgroup I.Gf where
  carrier := {x | (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL (lamAf (F := I.F) I.L) ∧
      ∀ y ∈ lamAf (F := I.F) I.L, ∃ z ∈ lamAf (F := I.F) I.L,
        ((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) - 1 : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ y =
          (g : I.E ⊗[I.F] Af I.F) • z}
  one_mem' := ⟨(Formalism.UG.stabGL _).one_mem, fun y hy => ⟨0, Submodule.zero_mem _, by simp⟩⟩
  mul_mem' := by
    rintro x x' ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨(Formalism.UG.stabGL _).mul_mem hx hy, fun w hw => ?_⟩
    obtain ⟨z1, hz1, e1⟩ := hy' w hw
    obtain ⟨z2, hz2, e2⟩ := hx' w hw
    refine ⟨((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ z1 + z2,
      Submodule.add_mem _ ((hx z1).mp hz1) hz2, ?_⟩
    have key : ∀ (M N : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (v : Fin I.n → I.E ⊗[I.F] Af I.F),
        (M * N - 1) *ᵥ v = M *ᵥ ((N - 1) *ᵥ v) + (M - 1) *ᵥ v := by
      intro M N v
      simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.one_mulVec]
      abel
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [key, e1, e2, Matrix.mulVec_smul, smul_add]
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    have hxi := (Formalism.UG.stabGL (lamAf (F := I.F) I.L)).inv_mem hx
    refine ⟨by simpa using hxi, fun w hw => ?_⟩
    obtain ⟨z, hz, e⟩ := hx' w hw
    refine ⟨-((((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
      Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ z), Submodule.neg_mem _ ((hxi z).mp hz), ?_⟩
    have key : ∀ (M Mi : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)), Mi * M = 1 →
        ∀ v, (Mi - 1) *ᵥ v = -(Mi *ᵥ ((M - 1) *ᵥ v)) := by
      intro M Mi h v
      simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.one_mulVec, h]
      abel
    simp only [Subgroup.coe_inv]
    rw [key _ _ (Units.inv_mul _), e, Matrix.mulVec_smul, smul_neg]

instance borelSpace_Gf : BorelSpace I.Gf := ⟨rfl⟩

end Gf

end PI.IwaMeasEx.Sk

end
