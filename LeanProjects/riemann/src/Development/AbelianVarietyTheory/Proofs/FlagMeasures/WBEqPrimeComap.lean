import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.FixedConj

def adeleEquiv (D : Formalism.BasicNotions.D7) (hF : D.host.F = maximalRealSubfield D.host.E) :
    ReciprocityTheory.Aut.AL D.host.E ≃+* Formalism.IndefR.Lev.EAf D :=
  (GlobalTheory.StdFrame.tensCastR hF).symm.trans
    (Algebra.TensorProduct.comm (↥D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af ↥D.host.F) D.host.E).toRingEquiv

def primeComap {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] (ι : E ≃+* E')
    (w : HeightOneSpectrum (𝓞 E')) : HeightOneSpectrum (𝓞 E) where
  asIdeal := Ideal.comap (RingOfIntegers.mapRingEquiv ι) w.asIdeal
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    apply w.ne_bot
    have := congrArg (Ideal.map (RingOfIntegers.mapRingEquiv ι)) h
    rwa [Ideal.map_comap_of_surjective _ (RingOfIntegers.mapRingEquiv ι).surjective, Ideal.map_bot] at this

end GlobalTheory.FixedConj

end
