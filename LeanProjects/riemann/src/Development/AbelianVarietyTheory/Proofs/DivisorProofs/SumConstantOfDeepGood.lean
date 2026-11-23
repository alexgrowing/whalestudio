import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumComponentDegreesDivLeLatticeSlopeStatement

open GlobalTheory.CovTop GlobalTheory.BigTop Formalism.MainNotions

namespace GlobalTheory.CovTop

theorem sumC_of_deepGood : DeepGood → SumC := fun h =>
  Closed.imp h fun _ _ _ ⟨C, h0, a, h⟩ => ⟨C, h0, a, fun x hx hle ι p hp i hi Y hY => by
    obtain ⟨-, -, -, h4, -, h6, -, h8⟩ := h x hx hle ι p hp i hi Y hY
    exact GlobalTheory.T.sum_component_degrees_div_le_latticeSlope _ p.T _ Y _ _ p.fw.laws ⟨Nat.le_add_left 1 _, hi.le⟩ hY.1 hY.2.1 hY.2.2 (uM p i) h4 h6 h8⟩

end GlobalTheory.CovTop
