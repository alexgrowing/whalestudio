import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.LocalRingCardinality.SpanPowerMembership.Adelic

noncomputable section

open Polynomial IsDedekindDomain NumberField IsLocalRing
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.NcVal.AriEta

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem val_int (x : 𝓞 F) : Valued.v (((x : F) : v.adicCompletion F)) ≤ 1 := by
  have h : Valued.v (((x : F) : v.adicCompletion F)) = v.valuation F (x : F) :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : F)
  rw [h]
  exact v.valuation_le_one x

theorem val_int_lt (x : 𝓞 F) (hx : x ∈ v.asIdeal) : Valued.v (((x : F) : v.adicCompletion F)) < 1 := by
  have h : Valued.v (((x : F) : v.adicCompletion F)) = v.valuation F (x : F) :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : F)
  rw [h]
  exact (v.valuation_lt_one_iff_mem x).mpr hx

abbrev ψo : 𝓞 F →+* v.adicCompletion F := (algebraMap F (v.adicCompletion F)).comp (algebraMap (𝓞 F) F)

theorem ψo_apply (x : 𝓞 F) : ψo v x = ((x : F) : v.adicCompletion F) := rfl

def io (x : 𝓞 F) : v.adicCompletionIntegers F := ⟨ψo v x, val_int v x⟩

abbrev ρ : v.adicCompletionIntegers F →+* v.adicCompletion F := (v.adicCompletionIntegers F).toSubring.subtype

theorem ρ_io (x : 𝓞 F) : ρ v (io v x) = ψo v x := rfl

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

end Formalism.L2.SG.Pf.NcVal.AriEta
