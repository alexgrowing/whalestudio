import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HeckeProd

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.Host.HChar

variable {L : Type} [Field L] [NumberField L] (χ : HChar L)

theorem productRule : χ.ProductRule := hecke_product_rule L χ

theorem val_principal (S : Finset (HeightOneSpectrum (𝓞 L))) (hS : ∀ v, v ∉ S → χ.UnrAt v) (k : Lˣ) :
    (∏ᶠ (v : HeightOneSpectrum (𝓞 L)) (_ : v ∉ S), χ.val v ^ ordF v k) = (χ.inf k * ∏ v ∈ S, χ.locK v k)⁻¹ :=
  eq_inv_of_mul_eq_one_right (χ.productRule S hS k)

end Formalism.L2.Host.HChar
