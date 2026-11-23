import Formalism.LocalToGlobal.UnitaryNorms.CharExGen

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host Formalism.L2.Host.CharEx

namespace PI.GlobFormGenW

section Ext

open WithZero

end Ext

variable {L : Type} [Field L] [NumberField L]

def conjPrime₂ (σ : 𝓞 L ≃+* 𝓞 L) (P : HeightOneSpectrum (𝓞 L)) : HeightOneSpectrum (𝓞 L) :=
  HeightOneSpectrum.comap (σ : 𝓞 L →+* 𝓞 L) σ.surjective P

end PI.GlobFormGenW
