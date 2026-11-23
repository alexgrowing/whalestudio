import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelProductIndex.Development

open NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct

noncomputable section

namespace PI.LPI

theorem prV_tmul_eq_tmul_apply {F E : Type} [Field F] [NumberField F] [CommRing E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (e : E) (a : FiniteAdeleRing (𝓞 F) F) :
    prV (E := E) v (e ⊗ₜ[F] a) = e ⊗ₜ[F] (a v) := rfl

theorem coord_prV {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {ι : Type}
    [DecidableEq ι] (b : Module.Basis ι F E) (v : HeightOneSpectrum (𝓞 F)) (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F) (i : ι) :
    TensorProduct.equivFinsuppOfBasisLeft b (prV (E := E) v z) i =
      (TensorProduct.equivFinsuppOfBasisLeft b z i) v := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]; try rfl
  | tmul e a =>
    rw [prV_tmul_eq_tmul_apply, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply,
      TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
    simp only [Algebra.smul_def]
    rfl
  | add x y hx hy =>
    simp only [map_add, Finsupp.coe_add, Pi.add_apply, hx, hy]
    try rfl

theorem plInj : PLInj := by
  intro F E _ _ _ _ _ z hz
  let b := Module.finBasis F E
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  rw [map_zero]
  refine Finsupp.ext fun i => FiniteAdeleRing.ext F fun v => ?_
  rw [← coord_prV b v z i, hz v, map_zero]
  rfl

end PI.LPI
