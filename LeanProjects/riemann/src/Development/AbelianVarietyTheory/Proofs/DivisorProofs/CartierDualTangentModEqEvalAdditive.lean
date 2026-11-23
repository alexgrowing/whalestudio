import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorProjectiveDvdOfCoordDvdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualQuotientFormEqEvalStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

private theorem dualDistrib_eq_mul'_map {O M N : Type} [CommRing O] [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (φ : Module.Dual O M) (ψ : Module.Dual O N) (t : M ⊗[O] N) :
    dualDistrib O M N (φ ⊗ₜ ψ) t = LinearMap.mul' O O (TensorProduct.map φ ψ t) := by
  induction t with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul m n => simp [dualDistrib_apply]

theorem cartierDual_tangent_mod :
    ∀ (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [Module.Finite O A] [Module.Projective O A] [Coalgebra.IsCocomm O A] (a : O) (u : Cot O (CartierDual O A) →ₗ[O] O ⧸ Ideal.span {a}), ∃ (b : A) (z : A ⊗[O] A), cobOne O A b = a • z ∧ ∀ φ : CartierDual O A, u (dUnit O φ) = Ideal.Quotient.mk _ (φ b) := by
  intro O A _ _ _ _ _ _ a u
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_point_dual_quotient_form_eq_eval O A (Ideal.span {a})
    (u ∘ₗ AugCot.d (Bialgebra.counitAlgHom O (CartierDual O A)) ∘ₗ
      (CartierDual.toDual O A).symm.toLinearMap)
  have hb' : ∀ φ : CartierDual O A, u (dUnit O φ) = Ideal.Quotient.mk _ (φ b) := fun φ => hb φ.ofConv
  obtain ⟨y, hy⟩ := GlobalTheory.T.exists_eq_smul_of_dvd_dualDistrib O A A a (cobOne O A b) (fun φ ψ => by
    have hm := hb' (WithConv.toConv φ * WithConv.toConv ψ)
    rw [dUnit, AugCot.d_mul, map_add, map_smul, map_smul, ← dUnit, ← dUnit, hb', hb'] at hm
    simp only [Bialgebra.counitAlgHom_apply, CartierDual.counit_apply] at hm
    have hc : (WithConv.toConv φ * WithConv.toConv ψ).ofConv b =
        LinearMap.mul' O O (TensorProduct.map φ ψ (CoalgebraStruct.comul b)) := rfl
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, dualDistrib_eq_mul'_map,
      cobOne_apply]
    simp only [map_sub, TensorProduct.map_tmul, LinearMap.mul'_apply]
    rw [← hc, ← hm]
    simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_mul]
    ring)
  exact ⟨b, y, hy, hb'⟩

end GlobalTheory
