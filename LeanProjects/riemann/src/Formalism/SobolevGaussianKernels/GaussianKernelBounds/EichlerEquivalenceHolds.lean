import Mathlib
import Formalism.SobolevGaussianKernels.StatementEI

set_option linter.unusedSimpArgs false

namespace Formalism.SL.P

open Formalism.SL.IwahoriBlocks
theorem eichler_isometry_holds : Formalism.SL.IwahoriBlocks.EichIsom := by
  intro E _ _ V _ _ h x u s hH hxx hux hs v w
  have hxu : h x u = 0 := by rw [hH, hux, star_zero]
  have hxw : h x w = star (h w x) := hH w x
  have huw : h u w = star (h w u) := hH w u
  have hxv : h x v = star (h v x) := hH v x
  have huv : h u v = star (h v u) := hH v u
  simp only [eich, map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.map_smul,
    LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, hxx, hux, hxu, hxw, huw, starRingEnd_apply, star_add, star_sub, star_mul', star_star, mul_zero, add_zero, sub_zero]
  rw [← hs]
  ring

theorem eichler_move_holds : Formalism.SL.IwahoriBlocks.EichMove := by
  intro E _ _ V _ _ h x x' u s hH hux hux' v hv
  have hx'u : h x' u = 0 := by rw [hH, hux', star_zero]
  simp only [eich, map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.map_smul,
    LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, hv, hx'u, mul_zero, add_zero, sub_zero, zero_smul, zero_mul, smul_zero]
  module

theorem eichler_composition_holds : Formalism.SL.IwahoriBlocks.EichComp := by
  intro E _ _ V _ _ h x a b s t hH hxx hax hbx v
  have hxa : h x a = 0 := by rw [hH, hax, star_zero]
  simp only [eich, map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, hxx, hax, hbx, hxa, mul_zero, zero_mul, add_zero, sub_zero, zero_smul, smul_zero]
  module

theorem eichler_inverse_holds : Formalism.SL.IwahoriBlocks.EichInv := by
  have hc := eichler_composition_holds
  intro E _ _ V _ _ h x u s hH hxx hux hs v
  have hnx : h (-u) x = 0 := by simp [hux]
  refine ⟨?_, ?_⟩
  · rw [hc E V h x (-u) u (star s) s hH hxx hnx hux]
    have : star s + s + h u (-u) = 0 := by
      rw [map_neg, ← hs]; ring
    have h2 : star s + s + -(h u) u = 0 := by rw [← hs]; ring
    simp [eich, h2]
  · rw [hc E V h x u (-u) s (star s) hH hxx hux hnx]
    have : s + star s + h (-u) u = 0 := by
      rw [LinearMap.map_neg, LinearMap.neg_apply, ← hs]; ring
    have h2 : s + star s + -(h u) u = 0 := by rw [← hs]; ring
    simp [eich, h2]

theorem eichler_integrality_holds : Formalism.SL.IwahoriBlocks.EichInt := by
  intro E _ _ V _ _ h O abelian₂ x x' u s hH hO hint hu hb hsx hx'x hux hux' v hv hvx'
  have hx'u : h x' u = 0 := by rw [hH, hux', star_zero]
  have hvx : h v x = h v (x + x') := by simp [hvx']
  have key : eich h x u s (eich h x' u s v) = v + h v u • (x + x') - (h v x + h v u * h x' x) • (u + s • x) := by
    simp only [eich, map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.map_smul,
      LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, hvx', hx'u, mul_zero, add_zero, sub_zero, zero_smul, zero_mul, smul_zero]
    module
  rw [key]
  have hvu := hint v hv u hu
  have hk : h v x + h v u * h x' x ∈ O := O.add_mem (hvx ▸ hint v hv _ hb) (O.mul_mem hvu hx'x)
  exact abelian₂.sub_mem (abelian₂.add_mem hv (hO _ hvu _ hb)) (hO _ hk _ (abelian₂.add_mem hu hsx))

end Formalism.SL.P
