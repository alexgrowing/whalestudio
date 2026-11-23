import Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantProjectionRangeTrivial

noncomputable section

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem lattice_theorem_of_trace_formula (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h : InvariantDenominatorEllPBound) (hTh : IsotypicProjectorTraceFormula) : IsotypicProjectorTheoremField D :=
  lattice_theorem_of_interfaces D h (isotypic_submodules_span_top D h2) restriction_is_representation hom_space_is_representation (invariant_projection_exists D h2) hTh lattice_adapted_basis_exists hom_lattice_dividedPower_stable homRep_ell_bounded_by_target

end Formalism.MainNotions.G.GLWeightTheory
