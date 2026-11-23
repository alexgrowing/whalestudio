import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularSequencePrimeDivisors
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.regular_sequence_prime_divisors : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (y : Y) (U : Y.Opens) (hy : y ∈ U) (c : ℕ) (a : Fin c → Γ(Y, U)), IsRegularLocalRing (Y.presheaf.stalk y) → FinalTheorems.Rsp (Y.presheaf.stalk y) c (fun i => Y.presheaf.germ U y hy (a i)) → ∃ (w : Fin c → Y) (u : Fin c → Y.functionFieldˣ), Function.Injective w ∧ ∀ j, (u j : Y.functionField) = fnOf U (gen_mem hy) (a j) ∧ w j ⤳ y ∧ Order.coheight (w j) = 1 ∧ w j ∉ Y.basicOpen (a j) ∧ Scheme.ord (u j : Y.functionField) (w j) = 1 ∧ ∀ v, v ⤳ y → Order.coheight v = 1 → v ≠ w j → v ∈ Y.basicOpen (a j) := by
  first | exact @_root_.GlobalTheory.RegParPrime.exists_primeDivisors_of_regularParams | exact _root_.GlobalTheory.RegParPrime.exists_primeDivisors_of_regularParams | (intros; apply _root_.GlobalTheory.RegParPrime.exists_primeDivisors_of_regularParams <;> assumption)
