import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalShareSumBound
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_share_sum_bound : Hypotheses2 → GlobalTheory.Published.GreenCuspidal → Lifts fun Fm x _ ι _ _ _ _ => ∃ ψ₀ : ∀ k : Fin 2, AddChar (ZMod ((Fm.D x ι).host.g k)) ℂ, (∀ k, ψ₀ k ≠ 1) ∧ ∀ S : ∀ k : Fin 2, Finset (Formalism.MainNotions.ArithmeticCylinders.Tup (Fm.D x ι) k), (∀ k, ∀ t ∈ S k, ¬ Formalism.MainNotions.ArithmeticCylinders.goodAt (Fm.D x ι) k t) → Formalism.MainNotions.ArithmeticCylinders.locShare (Fm.D x ι) (fun k _ => Formalism.MainNotions.ArithmeticCylinders.eUk (Fm.D x ι) k (ψ₀ k)) 0 (S 0) + Formalism.MainNotions.ArithmeticCylinders.locShare (Fm.D x ι) (fun k _ => Formalism.MainNotions.ArithmeticCylinders.eUk (Fm.D x ι) k (ψ₀ k)) 1 (S 1) ≤ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) := by
  first | exact @GlobalTheory.CovTop.LocShareNum.locShares_le_exp | exact GlobalTheory.CovTop.LocShareNum.locShares_le_exp | (intros; apply GlobalTheory.CovTop.LocShareNum.locShares_le_exp <;> assumption)
