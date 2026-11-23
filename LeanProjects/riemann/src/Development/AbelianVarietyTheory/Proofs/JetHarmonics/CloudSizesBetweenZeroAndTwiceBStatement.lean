import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CloudSizesBetweenZeroAndTwiceB
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cloudSizes_between_zero_and_twice_b : ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L), 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → L.Sc + L.etaSz ≤ 2 * L.sc.b ∧ ∀ j, InR D j → (∀ τ, 0 ≤ wj D j τ ∧ wj D j τ ≤ 2 * L.sc.b) ∧ (∀ t, wj D j (plOf D (false, t)) ≤ 2 * L.sc.b') ∧ ∀ z, (numOf D L).w j z = wj D j (plOf D z) := by
  first | exact @GlobalTheory.RunDepth.sizes_le_two_mul | exact GlobalTheory.RunDepth.sizes_le_two_mul | (intros; apply GlobalTheory.RunDepth.sizes_le_two_mul <;> assumption)
