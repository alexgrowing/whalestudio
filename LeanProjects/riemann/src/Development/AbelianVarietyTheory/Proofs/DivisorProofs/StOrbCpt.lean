import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasOrbIntOfIsCompactCentConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteUnitaryGroupHaarIsMulRightInvariant
open MeasureTheory GlobalTheory.Orb

namespace GlobalTheory.PsCo.Pc1

theorem stOrbCpt : GlobalTheory.PsCo.Pc1.StOrbCpt := by
  intro n ε μ _ s hs hT dt _ _ y f hf hc
  haveI : μ.IsMulRightInvariant := GlobalTheory.haar_UJ_isMulRightInvariant n ε μ
  exact GlobalTheory.hasOrbInt_of_isCompact_cent_conj _ μ s hT dt (isProperOrbit_realUJ hs) y f hf hc

end GlobalTheory.PsCo.Pc1
