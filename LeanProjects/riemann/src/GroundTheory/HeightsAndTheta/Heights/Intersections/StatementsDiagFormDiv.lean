import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagOrd
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

def DiagFormDiv.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι ν κ : Type) [Fintype ι] [Fintype ν] [Fintype κ] (E : Type) [AddCommGroup E]
    [Module Ω E] (Φ : Type) [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (B : ChartBundle ℤ x 2 E)
    (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω),
    T.IsTwistedDualSec B φ → T.IsTwistedDualGen B φ → T.IsTwistedDetGen B e δ → (∃ i, x i ≠ 0) →
    ∀ a : Fin 2 → Φ, AlgebraicIndependent Ω a →
    ∀ (α : T.WBlk → ℕ) (d : MRing (T.wwIdx ι ν κ)), IsMultiHomog d α →
      d ∈ T.wwIdeal x δ e φ (a 0) (a 0) →
      ∃ (γ β : T.WBlk → ℕ) (s r : MRing (T.wwIdx ι ν κ)), IsMultiHomog s γ ∧ IsMultiHomog r β ∧
        (∀ k, α k + γ k + T.wwDeg 3 0 k = β k + T.wwDeg 0 1 k) ∧
        s ∉ T.wwIdeal x δ e φ (a 0) (a 0) ∧
        aeval (T.wwCoord x δ e φ (a 0) (a 1)) d * aeval (T.wwCoord x δ e φ (a 0) (a 1)) s =
          T.diagSec a * aeval (T.wwCoord x δ e φ (a 0) (a 1)) r

section Quot

variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]

theorem DiagFormDiv.mem_diag_of_quot (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (a : Fin 2 → Φ) (ha : AlgebraicIndependent Ω a) {n : ℕ} {g h : MRing (T.wwIdx ι ν κ)}
    (hg : IsMultiHomog g (T.wwDeg n 1)) (hh : IsMultiHomog h (T.wwDeg (n + 3) 0))
    (hq : aeval (T.wwCoord x δ e φ (a 0) (a 1)) g = T.diagSec a * aeval (T.wwCoord x δ e φ (a 0) (a 1)) h) :
    g ∈ T.wwIdeal x δ e φ (a 0) (a 0) := by
  have key : ∀ b : Fin 2 → Φ, (MvPolynomial.map (aeval b : MvPolynomial (Fin 2) Ω →ₐ[Ω] Φ).toRingHom)
      (DiagonalOrder.polyConeMap x δ e φ g * ∏ k, X k ^ T.wwDeg (n + 3) 0 k -
        C (X 1 - X 0) * DiagonalOrder.polyConeMap x δ e φ h * ∏ k, X k ^ T.wwDeg n 1 k) =
      C (aeval (T.wwCoord x δ e φ (b 0) (b 1)) g - (b 1 - b 0) * aeval (T.wwCoord x δ e φ (b 0) (b 1)) h) *
        ((∏ k, X k ^ T.wwDeg n 1 k) * ∏ k, X k ^ T.wwDeg (n + 3) 0 k) := by
    intro b
    have e1 := DiagRAux.multiConeMap_of_homog (T.wwCoord x δ e φ (b 0) (b 1)) g _ hg
    have e2 := DiagRAux.multiConeMap_of_homog (T.wwCoord x δ e φ (b 0) (b 1)) h _ hh
    rw [DiagonalOrder.multiConeMap_eq, RingHom.comp_apply] at e1 e2
    rw [map_sub, map_mul, map_mul, map_mul, e1, e2]
    simp only [map_prod, map_pow, map_X, map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, map_mul, aeval_X]
    ring
  have hZ : DiagonalOrder.polyConeMap x δ e φ g * ∏ k, X k ^ T.wwDeg (n + 3) 0 k -
      C (X 1 - X 0) * DiagonalOrder.polyConeMap x δ e φ h * ∏ k, X k ^ T.wwDeg n 1 k = 0 := by
    apply MvPolynomial.map_injective _ (algebraicIndependent_iff_injective_aeval.mp ha)
    rw [key a, hq, T.diagSec, sub_self, C_0, zero_mul, map_zero]
  have h0 := key (fun _ => a 0)
  rw [hZ, map_zero, sub_self, zero_mul, sub_zero] at h0
  have hm : ((∏ k, (X k : MvPolynomial T.WBlk Φ) ^ T.wwDeg n 1 k) * ∏ k, X k ^ T.wwDeg (n + 3) 0 k) ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k))
      (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k))
  have hv : aeval (T.wwCoord x δ e φ (a 0) (a 0)) g = 0 :=
    C_eq_zero.1 ((mul_eq_zero.1 h0.symm).resolve_right hm)
  by_contra hn
  exact (DiagRAux.not_mem_ker_iff_aeval_ne _ g _ hg).1 hn hv

end Quot

end

end GroundTheory.Heights₂.Heights.Inter
