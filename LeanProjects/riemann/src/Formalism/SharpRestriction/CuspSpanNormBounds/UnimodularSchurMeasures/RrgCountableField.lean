import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix
open scoped TensorProduct
open Formalism.MainNotions.S

theorem rrg_P_mul_inv (I : AutInst) (v : InfinitePlace I.F) : I.P v * (I.P v)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))

theorem rrg_P_inv_mul (I : AutInst) (v : InfinitePlace I.F) : (I.P v)⁻¹ * I.P v = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))

theorem rrg_one_mem (I : AutInst) : (1 : I.GA) ∈ I.GFset := by
  refine ⟨1, Subgroup.one_mem _, fun v => ?_, ?_⟩
  · simp [rrg_P_inv_mul]
  · simp

theorem rrg_mul_mem (I : AutInst) {x y : I.GA} (hx : x ∈ I.GFset) (hy : y ∈ I.GFset) : x * y ∈ I.GFset := by
  obtain ⟨γ, hγ, hx1, hx2⟩ := hx
  obtain ⟨δ, hδ, hy1, hy2⟩ := hy
  refine ⟨γ * δ, Subgroup.mul_mem _ hγ hδ, fun v => ?_, ?_⟩
  · show uMat (x.1 v) * uMat (y.1 v) = _
    rw [hx1 v, hy1 v, Units.val_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (I.P v) (I.P v)⁻¹, rrg_P_mul_inv, Matrix.one_mul]
  · show I.fmat x.2 * I.fmat y.2 = _
    rw [hx2, hy2, Units.val_mul, Matrix.map_mul]

theorem rrg_inv_mem (I : AutInst) {x : I.GA} (hx : x ∈ I.GFset) : x⁻¹ ∈ I.GFset := by
  obtain ⟨γ, hγ, hx1, hx2⟩ := hx
  refine ⟨γ⁻¹, Subgroup.inv_mem _ hγ, fun v => ?_, ?_⟩
  · refine Units.inv_eq_of_mul_eq_one_right ?_
    show uMat (x.1 v) * _ = 1
    rw [hx1 v]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (I.P v) (I.P v)⁻¹, rrg_P_mul_inv, Matrix.one_mul,
      ← Matrix.mul_assoc (Matrix.map _ _) (Matrix.map _ _), ← Matrix.map_mul, Units.mul_inv,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, rrg_P_inv_mul]
  · refine Units.inv_eq_of_mul_eq_one_right ?_
    show I.fmat x.2 * _ = 1
    rw [hx2, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

def rr_GF (I : AutInst) : Subgroup I.GA where
  carrier := I.GFset
  mul_mem' := fun hx hy => rrg_mul_mem I hx hy
  one_mem' := rrg_one_mem I
  inv_mem' := fun hx => rrg_inv_mem I hx

theorem rr_GF_coe (I : AutInst) : ((rr_GF I : Subgroup I.GA) : Set I.GA) = I.GFset := rfl

theorem rr_mem_GF (I : AutInst) (x : I.GA) : x ∈ rr_GF I ↔ x ∈ I.GFset := Iff.rfl

theorem rrg_countable_field (E : Type) [Field E] [NumberField E] : Countable E :=
  (Module.Free.chooseBasis ℚ E).equivFun.injective.countable

theorem rrg_countable_GL (E : Type) [Field E] [NumberField E] (n : ℕ) : Countable (GL (Fin n) E) := by
  haveI := rrg_countable_field E
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  exact Function.Injective.countable (f := fun u : GL (Fin n) E => (u : Matrix (Fin n) (Fin n) E))
    (fun a b h => Units.ext h)

instance rr_GF_countable (I : AutInst) : Countable (rr_GF I) := by
  have := rrg_countable_GL I.E I.n
  refine Function.Injective.countable (f := fun x : rr_GF I => (x.2 : (x : I.GA) ∈ I.GFset).choose) ?_
  intro x y hxy
  have hx := (x.2 : (x : I.GA) ∈ I.GFset).choose_spec
  have hy := (y.2 : (y : I.GA) ∈ I.GFset).choose_spec
  simp only at hxy
  rw [hxy] at hx
  apply Subtype.ext
  apply Prod.ext
  · funext v
    apply Subtype.ext
    apply Units.ext
    exact (hx.2.1 v).trans (hy.2.1 v).symm
  · apply Subtype.ext
    apply Units.ext
    exact hx.2.2.trans hy.2.2.symm

end Formalism.MainNotions.LeviCoordinates

end
