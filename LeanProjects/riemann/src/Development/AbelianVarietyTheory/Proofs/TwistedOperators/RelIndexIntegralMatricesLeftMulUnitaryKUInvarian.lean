import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemIntMat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.InertHomIdx

open Formalism.UG in

theorem intMat_map_lmul_of_mem_range {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
    {r n : ℕ} {g : GL (Fin r) L} (hg : g ∈ (Formalism.UG.bc (n := Fin r) (intL L).subtype).range) :
    (intMat L r n).map (lmul (n := n) (g : Matrix (Fin r) (Fin r) L)) = intMat L r n := by
  obtain ⟨h, rfl⟩ := hg
  have hint : ∀ (a : GL (Fin r) (intL L)) (X : Matrix (Fin r) (Fin n) L), X ∈ intMat L r n →
      lmul (n := n) ((Formalism.UG.bc (n := Fin r) (intL L).subtype a : GL (Fin r) L) : Matrix (Fin r) (Fin r) L) X
        ∈ intMat L r n := by
    intro a X hX i j
    rw [lmul_apply, Matrix.mul_apply]
    refine Subring.sum_mem _ fun k _ => Subring.mul_mem _ ?_ (hX k j)
    exact ((a : Matrix (Fin r) (Fin r) (intL L)) i k).2
  apply le_antisymm
  · rintro _ ⟨X, hX, rfl⟩
    exact hint h X hX
  · intro X hX
    refine ⟨lmul (n := n) ((Formalism.UG.bc (n := Fin r) (intL L).subtype h⁻¹ : GL (Fin r) L) : Matrix (Fin r) (Fin r) L) X,
      hint h⁻¹ X hX, ?_⟩
    simp only [lmul_apply]
    rw [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mul]

theorem relIndex_intMat_lmul_KU {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
    (c : L →+* L) (r n : ℕ) (t k₁ k₂ : GU c r) (hk₁ : k₁ ∈ KU c r) (hk₂ : k₂ ∈ KU c r) :
    (intMat L r n).relIndex ((intMat L r n).map (lmul (k₁ * t * k₂).1.1)) =
      (intMat L r n).relIndex ((intMat L r n).map (lmul t.1.1)) := by
  have h₁ := intMat_map_lmul_of_mem_range (n := n) ((Subgroup.mem_subgroupOf.mp hk₁)).2
  have h₂ := intMat_map_lmul_of_mem_range (n := n) ((Subgroup.mem_subgroupOf.mp hk₂)).2
  have hcomp : (lmul (n := n) (k₁ * t * k₂).1.1) =
      (lmul (n := n) k₁.1.1).comp ((lmul (n := n) t.1.1).comp (lmul (n := n) k₂.1.1)) := by
    ext X : 1
    simp only [lmul_apply, AddMonoidHom.comp_apply, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
  have hinj : Function.Injective (lmul (n := n) k₁.1.1) := by
    intro X Y hXY
    have := congrArg (fun Z => ((k₁.1⁻¹ : GL (Fin r) L) : Matrix (Fin r) (Fin r) L) * Z) hXY
    simpa only [lmul_apply, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul] using this
  rw [hcomp, ← AddSubgroup.map_map, ← AddSubgroup.map_map, h₂]
  calc _ = ((intMat L r n).map (lmul (n := n) k₁.1.1)).relIndex
        (((intMat L r n).map (lmul (n := n) t.1.1)).map (lmul (n := n) k₁.1.1)) := by rw [h₁]
    _ = _ := AddSubgroup.relIndex_map_map_of_injective _ _ hinj

end GlobalTheory.InertHomIdx
end
