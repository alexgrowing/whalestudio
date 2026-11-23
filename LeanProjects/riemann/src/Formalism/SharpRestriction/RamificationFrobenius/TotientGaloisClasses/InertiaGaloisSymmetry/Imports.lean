import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.KcDiff
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.KcEqOfPowEqOne

open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors

noncomputable section

namespace Formalism.HC.Der

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

variable {φ : Frame} (H : HostRaw φ)

example (D : HostDer H) : type_of% D.splitK := splitK H
example (C : HostCore H) (D : HostDer H) : type_of% D.ordinary := ordinary H C
example (C : HostCore H) (D : HostDer H) : type_of% D.eta := eta H C
example (C : HostCore H) (D : HostDer H) : type_of% D.diffSupport := diffSupport H C
example (C : HostCore H) (D : HostDer H) : type_of% D.principal := principal H C
example (D : HostDer H) : type_of% D.unimodular := unimodular H
example (C : HostCore H) (D : HostDer H) : type_of% D.discr_sq := discr_sq H C
example (C : HostCore H) (D : HostDer H) : type_of% D.norm_mu := norm_mu H C

end Formalism.HC.Der

end
