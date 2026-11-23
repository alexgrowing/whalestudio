import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.DenomHolds

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets NumberField IsDedekindDomain Formalism.BasicNotions
  Formalism.L2.SG.HidaSetting
open scoped TensorProduct Matrix

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)

theorem hform_iota2 (hθ : IsSplitEquiv X p θ) (l l' : Fin X.B.I.n → X.B.I.E) :
    iota2 X p θ (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l l') =
      (fun j => iota2 X p θ (l' j)) ⬝ᵥ (J1 X p θ *ᵥ fun j => iota1 X p θ (l j)) := by
  simp only [secondEmbedding_eq_star X p θ hθ, Formalism.UG.hform, star_sum, star_mul', starRingEnd_apply, star_star,
    herm_entry, map_sum, map_mul, dotProduct, Matrix.mulVec, firstForm_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

theorem hform_iota1 (hθ : IsSplitEquiv X p θ) (l x : Fin X.B.I.n → X.B.I.E) :
    iota1 X p θ (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l x) =
      (fun j => iota2 X p θ (l j)) ⬝ᵥ (J1 X p θ *ᵥ fun j => iota1 X p θ (x j)) := by
  simp only [Formalism.UG.hform, map_sum, map_mul, dotProduct, Matrix.mulVec, firstForm_apply, starRingEnd_apply,
    ← secondEmbedding_eq_star X p θ hθ, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

theorem firstEmbedding_algebraMap (f : X.B.I.F) : iota1 X p θ (algebraMap X.B.I.F X.B.I.E f) = algebraMap X.B.I.F (FpX X p) f := by
  show ((θ (Algebra.TensorProduct.includeRight (algebraMap X.B.I.F X.B.I.E f))).1) = _
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply X.B.I.F (FpX X p) (TpX X p), AlgEquiv.commutes]
  simp

def DenseF : Prop :=
  ∀ c ε : FpX X p, ε ≠ 0 → ∃ b : X.B.I.F, ∃ o ∈ OpX X p, algebraMap X.B.I.F (FpX X p) b - c = ε * o

def EpsLat : Prop :=
  ∃ ε : FpX X p, ε ≠ 0 ∧ ∀ u : Fin X.B.I.n → FpX X p, (∀ i, u i ∈ OpX X p) →
    ε • u ∈ Mlat1 X p θ ∧ ε • u ∈ Mlat2 X p θ

theorem approx_of (hθ : IsSplitEquiv X p θ) (hD : DenseF X p) (hE : EpsLat X p θ) : ApproxP X p θ := by
  intro z hz
  obtain ⟨ε, hε0, hε⟩ := hE
  obtain ⟨a, w, hw, hwa⟩ := unitElt_holds X p θ hθ
  set α1 := iota1 X p θ (a : X.B.I.E) with hα1
  set α2 := iota2 X p θ (a : X.B.I.E) with hα2
  have val : ∀ β : FpX X p, ∃ d : FpX X p, d ≠ 0 ∧ d ∈ OpX X p ∧ d * β ∈ OpX X p := by
    intro β
    by_cases hβ : β ∈ OpX X p
    · exact ⟨1, one_ne_zero, one_mem _, by simpa using hβ⟩
    · have hβ0 : β ≠ 0 := fun h => hβ (h ▸ zero_mem _)
      refine ⟨β⁻¹, inv_ne_zero hβ0, ?_, by rw [inv_mul_cancel₀ hβ0]; exact one_mem _⟩
      exact ((OpX X p).mem_or_inv_mem β).resolve_left hβ
  obtain ⟨d1, hd10, hd1, hd1α⟩ := val α1
  obtain ⟨d2, hd20, hd2, hd2α⟩ := val α2
  have hδ0 : d1 * d2 ≠ 0 := mul_ne_zero hd10 hd20
  have hδ1 : d1 * d2 * α1 ∈ OpX X p := by
    rw [mul_right_comm]
    exact mul_mem hd1α hd2
  have hδ2 : d1 * d2 * α2 ∈ OpX X p := by
    rw [mul_assoc]
    exact mul_mem hd1 hd2α
  have hεδ : ε * (d1 * d2) ≠ 0 := mul_ne_zero hε0 hδ0
  choose b o ho hb using fun j => hD (w * z j * α1) (ε * (d1 * d2)) hεδ
  choose b' o' ho' hb' using fun j => hD (-(w * z j)) (ε * (d1 * d2)) hεδ
  set x : Fin X.B.I.n → X.B.I.E := fun j =>
    algebraMap X.B.I.F X.B.I.E (b j) + algebraMap X.B.I.F X.B.I.E (b' j) * (a : X.B.I.E) with hx
  set u1 : Fin X.B.I.n → FpX X p := fun j => d1 * d2 * o j + o' j * (d1 * d2 * α1) with hu1
  set u2 : Fin X.B.I.n → FpX X p := fun j => d1 * d2 * o j + o' j * (d1 * d2 * α2) with hu2
  have hu1m : ∀ j, u1 j ∈ OpX X p := fun j =>
    add_mem (mul_mem (mul_mem hd1 hd2) (ho j)) (mul_mem (ho' j) hδ1)
  have hu2m : ∀ j, u2 j ∈ OpX X p := fun j =>
    add_mem (mul_mem (mul_mem hd1 hd2) (ho j)) (mul_mem (ho' j) hδ2)
  have e1 : (fun j => iota1 X p θ (x j)) = ε • u1 := by
    funext j
    simp only [hx, hu1, map_add, map_mul, firstEmbedding_algebraMap, Pi.smul_apply, smul_eq_mul]
    rw [← hα1]
    linear_combination hb j + α1 * hb' j
  have e2 : (fun j => iota2 X p θ (x j)) = z + ε • u2 := by
    funext j
    simp only [hx, hu2, map_add, map_mul, secondEmbedding_algebraMap, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [← hα2]
    linear_combination hb j + α2 * hb' j + z j * hwa
  have M1mem : ε • u1 ∈ Mlat1 X p θ := (hε u1 hu1m).1
  have M2mem : ε • u2 ∈ Mlat2 X p θ := (hε u2 hu2m).2
  have mem1 : ∀ l ∈ X.B.I.L, (fun j => iota1 X p θ (l j)) ∈ Mlat1 X p θ := fun l hl =>
    Submodule.subset_span ⟨l, hl, rfl⟩
  have mem2 : ∀ l ∈ X.B.I.L, (fun j => iota2 X p θ (l j)) ∈ Mlat2 X p θ := fun l hl =>
    Submodule.subset_span ⟨l, hl, rfl⟩
  refine ⟨x, fun l hl => ⟨?_, ?_⟩, ?_⟩
  · rw [hform_iota1 X p θ hθ, e1]
    exact dual_fwd X p θ hθ _ (mem2 l hl) _ M1mem
  · rw [hform_iota2 X p θ hθ, e2, add_dotProduct]
    exact add_mem (hz _ (mem1 l hl)) (dual_fwd X p θ hθ _ M2mem _ (mem1 l hl))
  · rw [e2, sub_add_cancel_left]
    exact neg_mem M2mem

end Loc

end MassDataIdxSteps
