import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrossNormallyAtOfForallMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Discrepancy GlobalTheory.Cartier GlobalTheory.QCoh
open GlobalTheory.TopForm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_ord_sub_one_le_ord_wedgeDifferentials : ∀ {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    [LocallyOfFiniteType p] {n : ℕ}, topologicalKrullDim X = n → ∀ (E : DivOver p) {U : X.Opens} {y : X}
    (hy : y ∈ U), E.Through y → ∀ (z : Fin n → Γ(X, U)), formOf U (gen_mem hy) (dOn p z) ≠ 0 →
    ∀ {J : Type} [Fintype J] (e : J → Fin n), Function.Injective e → ∀ (u : J → X.functionFieldˣ),
    (∀ j, (u j : X.functionField) = fnOf U (gen_mem hy) (z (e j))) →
    ∑ j, E.ord (u j) - 1 ≤ E.formOrd (formOf U (gen_mem hy) (dOn p z)) := by
  first | exact @GlobalTheory.Discrepancy.DivOver.sum_ord_sub_one_le_formOrd_dOn | exact GlobalTheory.Discrepancy.DivOver.sum_ord_sub_one_le_formOrd_dOn | (intros; apply GlobalTheory.Discrepancy.DivOver.sum_ord_sub_one_le_formOrd_dOn <;> assumption)
