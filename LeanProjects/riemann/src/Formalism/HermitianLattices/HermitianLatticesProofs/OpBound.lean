import Mathlib
import Formalism.HermitianLattices.StatementMaj

open NumberField Matrix

noncomputable section

namespace Formalism.HermitianLatticesTheory

section OpBoundAux

variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

theorem opBound_cnorm_nonneg (u : ι → ℂ) : 0 ≤ cnorm u := Real.sqrt_nonneg _

theorem opBound_cnorm_sq (u : ι → ℂ) : cnorm u ^ 2 = ∑ i, ‖u i‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)

theorem opBound_normSq (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (z : V) :
    ‖realize b X z‖ ^ 2 = ∑ v, cnorm (fcoord b X v z) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Fintype.sum_prod_type, opBound_cnorm_sq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_two]
  show ‖realizeRaw b X z (v, i, 0)‖ ^ 2 + ‖realizeRaw b X z (v, i, 1)‖ ^ 2 = _
  simp only [realizeRaw, AddMonoidHom.coe_mk, ZeroHom.coe_mk, if_neg (by decide : (1 : Fin 2) ≠ 0),
    if_true, Real.norm_eq_abs, sq_abs, Complex.sq_norm,
    Complex.normSq_apply]
  ring

theorem opBound_vecAt_sub (b : Module.Basis ι K V) (v : InfinitePlace K) (x y : V) :
    vecAt b v (x - y) = vecAt b v x - vecAt b v y := by
  funext i; simp [vecAt, map_sub]

theorem opBound_vecAt_map (b : Module.Basis ι K V) (v : InfinitePlace K) (g : V →ₗ[K] V) (y : V) :
    vecAt b v (g y) = matAt b v g *ᵥ vecAt b v y := by
  funext i
  simp only [vecAt, matAt]
  rw [← LinearMap.toMatrix_mulVec_repr b b g y, RingHom.map_mulVec]
  rfl

theorem opBound_fcoord (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (g : V →ₗ[K] V) (y : V) :
    fcoord b X v (g y - y) = (X v)⁻¹ *ᵥ ((matAt b v g - 1) *ᵥ vecAt b v y) := by
  rw [fcoord, opBound_vecAt_sub, opBound_vecAt_map, Matrix.sub_mulVec, Matrix.one_mulVec]

end OpBoundAux

theorem opBound : OpBound := by
  intro K V ι _ _ _ _ _ _ _ b X g δ hδ hO y
  have hb : ∀ v, cnorm (fcoord b X v (g y - y)) ≤ δ * cnorm (fcoord b X v y) := by
    intro v
    rw [opBound_fcoord]
    exact hO v (vecAt b v y)
  have hsq : ‖realize b X (g y - y)‖ ^ 2 ≤ (δ * ‖realize b X y‖) ^ 2 := by
    rw [mul_pow, opBound_normSq, opBound_normSq, Finset.mul_sum]
    refine Finset.sum_le_sum fun v _ => ?_
    calc cnorm (fcoord b X v (g y - y)) ^ 2 ≤ (δ * cnorm (fcoord b X v y)) ^ 2 :=
          pow_le_pow_left₀ (opBound_cnorm_nonneg _) (hb v) 2
      _ = δ ^ 2 * cnorm (fcoord b X v y) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

end Formalism.HermitianLatticesTheory
