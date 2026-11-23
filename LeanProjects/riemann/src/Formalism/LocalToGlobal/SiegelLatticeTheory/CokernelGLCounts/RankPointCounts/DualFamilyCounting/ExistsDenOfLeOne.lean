import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsUnitDetOfIsometry
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsSubDivMemSP

noncomputable section

namespace Formalism.L2.SG.Pf.Lem3Mass

open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.UnitaryGroupLocal
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology Filter

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (v : HeightOneSpectrum (𝓞 F))

section Trace

variable (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (hfix : ∀ y : E, σ y = y → y ∈ (algebraMap F E).range)

def trF (y : E) : F :=
  Classical.choose (hfix (y + σ y) (by rw [map_add, hσ, add_comm]))

theorem trF_spec (y : E) : algebraMap F E (trF σ hσ hfix y) = y + σ y :=
  Classical.choose_spec (hfix (y + σ y) (by rw [map_add, hσ, add_comm]))

theorem trF_add (y z : E) : trF σ hσ hfix (y + z) = trF σ hσ hfix y + trF σ hσ hfix z := by
  apply (algebraMap F E).injective
  rw [map_add, trF_spec, trF_spec, trF_spec, map_add]
  abel

theorem trF_smul (c : F) (y : E) : trF σ hσ hfix (c • y) = c * trF σ hσ hfix y := by
  apply (algebraMap F E).injective
  rw [map_mul, trF_spec, trF_spec, Algebra.smul_def, map_mul, AlgHom.commutes, mul_add]

def trA : E ⊗[F] v.adicCompletion F →ₗ[F] v.adicCompletion F :=
  TensorProduct.lift (LinearMap.mk₂ F (fun (e : E) (r : v.adicCompletion F) => trF σ hσ hfix e • r)
    (fun e e' r => by rw [trF_add, add_smul])
    (fun c e r => by rw [trF_smul, mul_smul])
    (fun e r r' => by rw [smul_add])
    (fun c e r => by rw [smul_comm]))

end Trace

section D1

variable (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (hfix : ∀ y : E, σ y = y → y ∈ (algebraMap F E).range)

theorem coe_algebraMap_int (t : 𝓞 F) :
    algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) t) = algebraMap F E (t : F) := by
  rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, IsScalarTower.algebraMap_apply (𝓞 F) F E]

end D1

end Formalism.L2.SG.Pf.Lem3Mass
