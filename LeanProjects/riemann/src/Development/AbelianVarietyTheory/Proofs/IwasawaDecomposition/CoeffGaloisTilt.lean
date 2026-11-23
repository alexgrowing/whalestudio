import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.AdicMaps

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem coeff_galois_tilt (l : ℕ) [Fact l.Prime] (g : GQ l) (x : OCb l) (n : ℕ) (y : OC l)
    (h : PreTilt.coeff n x = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y) :
    ∃ y' : OC l, (y' : PadicComplex l) = Per.σC g (y : PadicComplex l) ∧
      PreTilt.coeff n (Per.σF g x) = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y' :=
  ⟨Per.σO g y, GlobalTheory.RingIface.sigO_coe (l := l) g y,
    GlobalTheory.AdicMaps.coeff_galois l g x n y h⟩

end GlobalTheory.MemLoc
