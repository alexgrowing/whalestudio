import Mathlib
import GroundTheory.PAdicHodge.SlopeRobbaPure
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Module

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsDiscreteValuationRing (normInteger K)]

namespace PhiModule

universe u

variable {F : FrobeniusLift K}
variable {M : Type u} [AddCommGroup M] [Module (Robba K) M] [Module.Free (Robba K) M]
  [Module.Finite (Robba K) M]

variable (F) in

def IsSemistableSubquot (Φ : M →ₛₗ[F.phi] M) (N N' : Submodule (Robba K) M) (h : IsStable Φ N)
    (h' : IsStable Φ N') [Module.IsTorsionFree (Robba K) (M ⧸ N)]
    [Module.IsTorsionFree (Robba K) (M ⧸ N')] : Prop :=
  letI := free_subquot (N := N) (N' := N')
  letI := finite_subquot (N := N) (N' := N')
  IsSemistable F (subquot Φ N N' h h')

variable (F) in

def degSubquot (Φ : M →ₛₗ[F.phi] M) (N N' : Submodule (Robba K) M) (h : IsStable Φ N)
    (h' : IsStable Φ N') [Module.IsTorsionFree (Robba K) (M ⧸ N)]
    [Module.IsTorsionFree (Robba K) (M ⧸ N')] : ℤ :=
  letI := free_subquot (N := N) (N' := N')
  letI := finite_subquot (N := N) (N' := N')
  deg F.unitOrd (subquot Φ N N' h h')

variable (F) in

structure HNFiltration (Φ : M →ₛₗ[F.phi] M) where

  length : ℕ

  N : ℕ → Submodule (Robba K) M

  slope : ℕ → ℚ
  N_zero : N 0 = ⊥
  N_of_le : ∀ i, length ≤ i → N i = ⊤
  lt_succ : ∀ i, i < length → N i < N (i + 1)
  stable : ∀ i, IsStable Φ (N i)
  saturated : ∀ i, Module.IsTorsionFree (Robba K) (M ⧸ N i)
  semistable : ∀ i, i < length →
    haveI := saturated i
    haveI := saturated (i + 1)
    IsSemistableSubquot F Φ (N i) (N (i + 1)) (stable i) (stable (i + 1))
  deg_eq : ∀ i, i < length →
    haveI := saturated i
    haveI := saturated (i + 1)
    (degSubquot F Φ (N i) (N (i + 1)) (stable i) (stable (i + 1)) : ℚ) =
      slope i * finrank (Robba K) (N (i + 1) ⧸ inSub (N i) (N (i + 1)))
  slope_lt : ∀ i j, i < j → j < length → slope i < slope j

theorem finrank_subquot_pos {N N' : Submodule (Robba K) M} (hlt : N < N')
    [Module.IsTorsionFree (Robba K) (M ⧸ N)] [Module.IsTorsionFree (Robba K) (M ⧸ N')] :
    0 < finrank (Robba K) (N' ⧸ inSub N N') := by
  have := free_subquot (N := N) (N' := N')
  have := finite_subquot (N := N) (N' := N')
  have := isTorsionFree_subquot (N := N) (N' := N')
  rw [Module.finrank_pos_iff_exists_ne_zero]
  obtain ⟨x, hx, hxN⟩ := SetLike.exists_of_lt hlt
  refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, fun h0 => hxN ?_⟩
  rw [Submodule.Quotient.mk_eq_zero] at h0
  exact h0

def HNFiltration.toSlopeFiltration {Φ : M →ₛₗ[F.phi] M}
    (hss : ∀ (M' : Type u) [AddCommGroup M'] [Module (Robba K) M'] [Module.Free (Robba K) M']
      [Module.Finite (Robba K) M'] (Φ' : M' →ₛₗ[F.phi] M'), IsSemistable F Φ' →
      0 < finrank (Robba K) M' → IsPure F Φ' ((deg F.unitOrd Φ' : ℚ) / finrank (Robba K) M'))
    (S : HNFiltration F Φ) : SlopeFiltration F Φ where
  length := S.length
  N := S.N
  slope := S.slope
  N_zero := S.N_zero
  N_of_le := S.N_of_le
  lt_succ := S.lt_succ
  stable := S.stable
  saturated := S.saturated
  pure i hi := by
    have := S.saturated i
    have := S.saturated (i + 1)
    have := free_subquot (N := S.N i) (N' := S.N (i + 1))
    have := finite_subquot (N := S.N i) (N' := S.N (i + 1))
    have hpos := finrank_subquot_pos (S.lt_succ i hi)
    have hp := hss _ _ (S.semistable i hi) hpos
    have hdeg := S.deg_eq i hi
    have hr : (finrank (Robba K) (S.N (i + 1) ⧸ inSub (S.N i) (S.N (i + 1))) : ℚ) ≠ 0 := by
      exact_mod_cast hpos.ne'
    change IsPure F (subquot Φ (S.N i) (S.N (i + 1)) (S.stable i) (S.stable (i + 1))) (S.slope i)
    change (degSubquot F Φ _ _ _ _ : ℚ) = _ at hdeg
    unfold degSubquot at hdeg
    rw [hdeg, mul_div_assoc, div_self hr, mul_one] at hp
    exact hp
  slope_lt := S.slope_lt

theorem nonempty_slopeFiltration_of {Φ : M →ₛₗ[F.phi] M}
    (hss : ∀ (M' : Type u) [AddCommGroup M'] [Module (Robba K) M'] [Module.Free (Robba K) M']
      [Module.Finite (Robba K) M'] (Φ' : M' →ₛₗ[F.phi] M'), IsSemistable F Φ' →
      0 < finrank (Robba K) M' → IsPure F Φ' ((deg F.unitOrd Φ' : ℚ) / finrank (Robba K) M'))
    (hHN : Nonempty (HNFiltration F Φ)) : Nonempty (SlopeFiltration F Φ) :=
  hHN.map (HNFiltration.toSlopeFiltration hss)

end PhiModule

end GroundTheory.PAdicHodge
