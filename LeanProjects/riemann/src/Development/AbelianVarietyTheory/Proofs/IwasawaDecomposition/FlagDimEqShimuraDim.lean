import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceDimensionEqSumChoose
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoMulCardPsi
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam.SigDim

theorem dim_add_sum_choose_eq_dimFl : ∀ {D : D7} {A : Amb D} {N j : ℕ} (S : Sig A N j),
    S.Dw.dim + ∑ τ, (S.Dw.mult τ).choose 2 = Formalism.DegreeFormula.dimFl D.what₂.Tau N := by
  intro D A N j S
  rw [GlobalTheory.FlagDimSum.dim_add_sum_choose, S.rank_eq, Formalism.DegreeFormula.dimFl, GlobalTheory.ShFam.CmDim.card_tau]

end GlobalTheory.ShFam.SigDim
