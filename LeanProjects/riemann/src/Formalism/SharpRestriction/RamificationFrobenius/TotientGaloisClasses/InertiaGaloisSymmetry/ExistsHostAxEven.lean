import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.OfRawToHostRaw
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.AnyLevel

noncomputable section

namespace Formalism.HC

open Formalism.FrobeniusOrbits

def CharData.toHostAx {φ : Frame} (D : CharData φ) : HostAx φ := HostAx.ofRaw D.toHostRaw

variable {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ)

end Formalism.HC

end
