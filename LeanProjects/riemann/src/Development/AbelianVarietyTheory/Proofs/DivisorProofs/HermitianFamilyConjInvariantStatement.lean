import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFamilyConjInvariant
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
open NumberField ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_family_conj_invariant : ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K) (h : HermFam K (Fin F.P₀.g → K)), F.IsHerm h → GlobalTheory.Published.ConjInv h := by
  first | exact @GlobalTheory.LieHt.SemiFibConj.conjInv | exact GlobalTheory.LieHt.SemiFibConj.conjInv | (intros; apply GlobalTheory.LieHt.SemiFibConj.conjInv <;> assumption)
