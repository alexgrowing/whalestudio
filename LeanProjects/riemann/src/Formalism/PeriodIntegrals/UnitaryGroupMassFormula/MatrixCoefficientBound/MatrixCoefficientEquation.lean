import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.PermRepApply
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.GammaMatrixInverse

open Finset Matrix

open scoped ComplexConjugate

noncomputable section

open Classical

namespace PI.GGMatBoundW

open Formalism.L2.SG.GGMirabolic

section General

variable {G : Type} [Group G] {X : Type} [MulAction Gᵐᵒᵖ X]

theorem eq_of_smul_eq_of_free (hfree : ∀ (x : Gᵐᵒᵖ) (j : X), x • j = j → x = 1) {a b : Gᵐᵒᵖ} {j : X}
    (h : a • j = b • j) : a = b := by
  have h1 : (b⁻¹ * a) • j = j := by rw [mul_smul, h, inv_smul_smul]
  exact (inv_mul_eq_one.mp (hfree _ _ h1)).symm

theorem exists_smul_comm (i j : X) : (∃ x : Gᵐᵒᵖ, x • j = i) ↔ ∃ x : Gᵐᵒᵖ, x • i = j :=
  ⟨fun ⟨x, hx⟩ => ⟨x⁻¹, by rw [← hx, inv_smul_smul]⟩, fun ⟨x, hx⟩ => ⟨x⁻¹, by rw [← hx, inv_smul_smul]⟩⟩

theorem sum_orbit [Fintype G] (hfree : ∀ (x : Gᵐᵒᵖ) (j : X), x • j = j → x = 1) (d : X → X → G)
    (hd : ∀ i j, (∃ x : Gᵐᵒᵖ, x • j = i) → MulOpposite.op (d i j) • j = i) (f : G → ℂ) (i j : X) :
    (∑ x : G, if MulOpposite.op x • j = i then f x else 0) =
      if ∃ x : Gᵐᵒᵖ, x • j = i then f (d i j) else 0 := by
  by_cases h : ∃ x : Gᵐᵒᵖ, x • j = i
  · rw [if_pos h]
    have hdij := hd i j h
    rw [Finset.sum_eq_single (d i j)]
    · rw [if_pos hdij]
    · intro b _ hb
      rw [if_neg]
      intro hbj
      exact hb (MulOpposite.op_injective (eq_of_smul_eq_of_free hfree (hbj.trans hdij.symm)))
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [if_neg]
    intro hx
    exact h ⟨_, hx⟩

end General

section Prod

variable {ι : Type} [Fintype ι] {Fq : ι → Type} [∀ v, Field (Fq v)] [∀ v, Fintype (Fq v)] {k : ℕ}

private theorem gam_inv_eq_conj {F : Type} [Field F] [Fintype F] {k : ℕ} (ψ₀ : AddChar F ℂ)
    (x : GL (Fin k) F) : gam ψ₀ x⁻¹ = conj (gam ψ₀ x) := by
  unfold gam
  simp only [map_mul, map_inv₀, map_natCast, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← psiNat_inv]
  congr 1
  group

theorem gamProd_inv (ψ : ∀ v, AddChar (Fq v) ℂ) (x : ∀ v, GL (Fin k) (Fq v)) :
    gamProd ψ x⁻¹ = conj (gamProd ψ x) := by
  unfold gamProd
  rw [map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Pi.inv_apply, gam_inv_eq_conj]

theorem toMatrix'_totOp_apply (ψ : ∀ v, AddChar (Fq v) ℂ) (X : Type) [Fintype X]
    [MulAction (∀ v, GL (Fin k) (Fq v))ᵐᵒᵖ X] (i j : X) :
    LinearMap.toMatrix' (totOp ψ (permRep (∀ v, GL (Fin k) (Fq v)) X)) i j =
      ∑ x : (∀ v, GL (Fin k) (Fq v)), if MulOpposite.op x • i = j then gamProd ψ x else 0 := by
  rw [LinearMap.toMatrix'_apply]
  simp [totOp, permRep, LinearMap.funLeft, Finset.sum_apply, Pi.single_apply, mul_ite]

end Prod

theorem totally_hermitian_form : TotHerm := by
  intro ι _ Fq _ _ k ψ X _ _
  refine Matrix.IsHermitian.ext fun i j => ?_
  rw [toMatrix'_totOp_apply, toMatrix'_totOp_apply, star_sum]
  refine Fintype.sum_equiv (Equiv.inv _) _ _ fun x => ?_
  have hiff : MulOpposite.op x • j = i ↔ MulOpposite.op x⁻¹ • i = j := by
    rw [MulOpposite.op_inv]
    constructor
    · intro h
      rw [← h, inv_smul_smul]
    · intro h
      rw [← h, smul_inv_smul]
  simp only [Equiv.inv_apply]
  split_ifs with h1 h2 h2
  · rw [gamProd_inv]
    rfl
  · exact absurd (hiff.mp h1) h2
  · exact absurd (hiff.mpr h2) h1
  · exact star_zero _

theorem matrix_coefficient_equation : MatrixEq := by
  intro ι _ Fq _ _ k ψ X _ _ hfree d hd
  constructor
  · ext i j
    rw [Matrix.of_apply, toMatrix'_totOp_apply, sum_orbit hfree d hd,
      exists_smul_comm (G := ∀ v, GL (Fin k) (Fq v)) i j]
    split_ifs with h
    · have h1 := hd j i h
      have h3 := hd i j ((exists_smul_comm (G := ∀ v, GL (Fin k) (Fq v)) i j).mpr h)
      have hdd : d j i = (d i j)⁻¹ := by
        apply MulOpposite.op_injective
        apply eq_of_smul_eq_of_free hfree (j := i)
        rw [h1, MulOpposite.op_inv]
        exact eq_inv_smul_iff.mpr h3
      rw [hdd, gamProd_inv]
    · rfl
  · ext i j
    rw [Matrix.of_apply, Matrix.transpose_apply, toMatrix'_totOp_apply, sum_orbit hfree d hd]

end PI.GGMatBoundW
