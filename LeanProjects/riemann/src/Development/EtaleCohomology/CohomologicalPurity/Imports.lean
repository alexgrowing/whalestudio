import Development.EtaleCohomology.CohomologicalPurity.LeafIndExc

namespace LateralTheory.CohomologicalPurity

theorem goal_of (hG : LeafGysin) (hS : LeafSemi) : Goal :=
  fun H => ⟨hG H, hS H.2.2.2.2.2.2.1 (hG H)⟩

end LateralTheory.CohomologicalPurity
