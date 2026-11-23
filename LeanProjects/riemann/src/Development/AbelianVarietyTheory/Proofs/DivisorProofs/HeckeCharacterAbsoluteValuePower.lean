import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import GroundTheory.GlobalFields.WeilGroups.QuasiCharacterDecomposition
import GroundTheory.GlobalFields.TateThesis.NonvanishingPrimes

open NumberField IsDedekindDomain Formalism.L2.Host

noncomputable section

namespace GlobalTheory.HeckeNormPow

def toQC {K : Type} [Field K] [NumberField K] (χ : HChar K) : GroundTheory.Global.QuasiCharacter K where
  toMonoidHom := QuotientGroup.lift _ χ.1 (by
    rintro _ ⟨a, rfl⟩
    exact χ.2.2 a)
  continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 χ.2.1

theorem norm_val_eq_rpow : ∀ (K : Type) [Field K] [NumberField K] (χ : HChar K), ∃ s : ℝ,
    ∀ w : HeightOneSpectrum (𝓞 K), ‖((χ.val w : ℂˣ) : ℂ)‖ = (Ideal.absNorm w.asIdeal : ℝ) ^ s := by
  intro K _ _ χ
  refine ⟨-(toQC χ).exponent, fun w => ?_⟩
  have h1 := (toQC χ).norm_apply
    (GroundTheory.Global.IdeleClassGroup.mk K (GroundTheory.Global.IdeleGroup.finiteEmbedding w (atFin w (unif w))))
  rw [GroundTheory.Global.IdeleClassGroup.ideleModule_mk,
    GroundTheory.Global.ideleModule_finiteEmbedding_of_uniformizer (unif_spec w)] at h1
  have h2 : ((χ.val w : ℂˣ) : ℂ) = (((toQC χ) (GroundTheory.Global.IdeleClassGroup.mk K
      (GroundTheory.Global.IdeleGroup.finiteEmbedding w (atFin w (unif w)))) : ℂˣ) : ℂ) := rfl
  rw [h2, h1, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity)]

end GlobalTheory.HeckeNormPow
