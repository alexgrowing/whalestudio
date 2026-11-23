import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdLiftDef

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat NumberField Module

section

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

def ladjG : Matrix (Fin S.rank) (Fin S.rank) E := fun i k => S.hT (S.frame i) (S.frame k)

theorem ladj_ext (y : S.V) (h : ∀ i, S.hT (S.frame i) y = 0) : y = 0 := by
  apply S.nondeg.2 y
  intro x
  have : S.hT.flip y = 0 := S.frame.ext (fun i => by simpa using h i)
  have h2 := LinearMap.congr_fun this x
  simpa using h2

theorem ladj_det : (ladjG S).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  apply hv
  have hy : ∑ k, v k • S.frame k = 0 := by
    apply ladj_ext S
    intro i
    rw [map_sum]
    have := congrFun hmul i
    simp only [Matrix.mulVec, dotProduct, ladjG, Pi.zero_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_smul, smul_eq_mul, mul_comm]
  funext k
  exact Fintype.linearIndependent_iff.1 S.frame.linearIndependent v hy k

def ladjOp (B : S.V →ₗ[E] S.V) : S.V →ₗ[E] S.V :=
  ∑ i, (∑ k, ((ladjG S)⁻¹ i k) • S.hT (B (S.frame k))).smulRight (S.frame i)

theorem ladj_frame (B : S.V →ₗ[E] S.V) (l : Fin S.rank) (y : S.V) :
    S.hT (S.frame l) (ladjOp S B y) = S.hT (B (S.frame l)) y := by
  have hu : IsUnit (ladjG S).det := isUnit_iff_ne_zero.2 (ladj_det S)
  simp only [ladjOp, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.smul_apply, map_sum, map_smul,
    smul_eq_mul]
  have h1 : ∀ i : Fin S.rank, (∑ k, (ladjG S)⁻¹ i k * S.hT (B (S.frame k)) y) * S.hT (S.frame l) (S.frame i) =
      ∑ k, (ladjG S l i * (ladjG S)⁻¹ i k) * S.hT (B (S.frame k)) y := by
    intro i
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [ladjG]
    ring
  rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_comm]
  have h2 : ∀ k : Fin S.rank, ∑ i, (ladjG S l i * (ladjG S)⁻¹ i k) * S.hT (B (S.frame k)) y =
      ((1 : Matrix (Fin S.rank) (Fin S.rank) E) l k) * S.hT (B (S.frame k)) y := by
    intro k
    rw [← Finset.sum_mul, ← Matrix.mul_nonsing_inv _ hu, Matrix.mul_apply]
  rw [Finset.sum_congr rfl (fun k _ => h2 k)]
  simp [Matrix.one_apply]

theorem ladj_adj (B : S.V →ₗ[E] S.V) : LAdj S B (ladjOp S B) := by
  intro x y
  have : (S.hT.flip y).comp B = S.hT.flip (ladjOp S B y) :=
    S.frame.ext (fun i => by simpa using (ladj_frame S B i y).symm)
  have h2 := LinearMap.congr_fun this x
  simpa using h2

end

theorem l_adj : IntegralAdjointUnimodular := by
  intro E _ _ _ S Λ hU B hB
  refine ⟨ladjOp S B, ladj_adj S B, fun l hl => ?_⟩
  have hd : Formalism.HermitianLatticesTheory.dual S.hT Λ = Λ := hU
  rw [← hd, Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
  intro y hy
  rw [← ladj_adj S B y l]
  have hl' : l ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by rw [hd]; exact hl
  exact (Formalism.HermitianLatticesTheory.dualBasic_mem_dual S.hT Λ l).1 hl' _ (hB y hy)

end Formalism.MainNotions.BridgeLemma

end
