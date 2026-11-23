import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.KappaRowsEntriesLeSizes
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kappaRows_entries_le_sizes : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (j : ℕ), InR D j → ∀ τ : D.what₂.Tau, (∀ i, i.1 < D.R.k - 1 → ((kaR Tp hK j).aP τ i : ℝ) ≤ wj D j τ + L.Sc) ∧ (∀ i, D.R.k - 1 ≤ i.1 → ((kaR Tp hK j).aP τ i : ℝ) ≤ L.etaSz) ∧ ∀ i, ((kaR Tp hK j).aM τ i : ℝ) ≤ L.etaSz := by
  first | exact @GlobalTheory.WeightRows.kappa_entries_le | exact GlobalTheory.WeightRows.kappa_entries_le | (intros; apply GlobalTheory.WeightRows.kappa_entries_le <;> assumption)
