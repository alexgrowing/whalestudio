import Formalism.SizeWindowBrackets.ChainSlopeWindows.GaloisMapComplexConjugation
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

noncomputable section

namespace UpperTheory.Comparison₂

open Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LHost

def toE (φ : Frame) : φ.GG →* Multiplicative (E0 × φ.A) where
  toFun g := Multiplicative.ofAdd ((Multiplicative.toAdd (sgn2 g.1.2), Multiplicative.toAdd (sgn2 g.1.1)), φ.iotaInv g.2)
  map_one' := by
    simp only [Prod.snd_one, Prod.fst_one, map_one]
    rfl
  map_mul' g h := by
    simp only [Prod.snd_mul, Prod.fst_mul, map_mul]
    rfl

variable {φ : Frame}

def recH (H : HostRaw φ) : (ZMod H.condN)ˣ →* Multiplicative (E0 × φ.A) := (toE φ).comp H.art

def arith (H : HostRaw φ) : ArithData φ.A := cftData H.q H.d (recH H)

end UpperTheory.Comparison₂

end
