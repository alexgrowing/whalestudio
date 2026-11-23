import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedBoundaryDivisorSum
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordUShimOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weighted_boundary_divisor_sum : ∀ {D : D7} (O : Setup D) (c : O.s.Comp) (la : D.what₂.Tau → Fin O.N → ℤ), ∑ x : DV.Rt D.what₂.Tau O.N, (-la x.1 x.2) • GlobalTheory.ShFam.Pad.divOf (O.Φ.C c) (O.ex x) = O.s.Lw O.L O.Φ c la := by
  first | exact @GlobalTheory.RootWeight.sum_neg_smul_divOf_ex_eq_Lw | exact GlobalTheory.RootWeight.sum_neg_smul_divOf_ex_eq_Lw | (intros; apply GlobalTheory.RootWeight.sum_neg_smul_divOf_ex_eq_Lw <;> assumption)
