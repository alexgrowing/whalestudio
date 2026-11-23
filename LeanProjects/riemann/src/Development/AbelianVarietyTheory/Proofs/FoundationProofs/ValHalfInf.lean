import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing

noncomputable section

namespace GlobalTheory.Eis.Conv

open scoped TensorProduct
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

def halfInf (F : Type) [Field F] [NumberField F] : (AF F)ˣ where
  val := (algebraMap F (Ainf F) 2⁻¹, 1)
  inv := (algebraMap F (Ainf F) 2, 1)
  val_inv := Prod.ext (by
    change algebraMap F (Ainf F) 2⁻¹ * algebraMap F (Ainf F) 2 = 1
    rw [← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]) (mul_one _)
  inv_val := Prod.ext (by
    change algebraMap F (Ainf F) 2 * algebraMap F (Ainf F) 2⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]) (mul_one _)

def halfE (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] : (AF F ⊗[F] E)ˣ :=
  Units.map (algebraMap (AF F) (AF F ⊗[F] E)).toMonoidHom (halfInf F)

theorem val_halfE (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] :
    (halfE F E).1 = (halfInf F).1 ⊗ₜ[F] (1 : E) := rfl

open scoped TensorProduct in
open NumberField in
theorem _root_.GlobalTheory.Eis.Conv.sigR_halfE {F E : Type} [Field F] [NumberField F] [Field E]
    [Algebra F E] (σ : E →ₐ[F] E) :
    _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ (_root_.GlobalTheory.Eis.Conv.halfE F E).1 =
      (_root_.GlobalTheory.Eis.Conv.halfE F E).1 := by
  simp [_root_.GlobalTheory.Eis.Conv.halfE, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.algebraMap_apply]

end GlobalTheory.Eis.Conv

end
