import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHilbertLatticeContainsAndCoordinateSize
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedHilbertLattice_contains_and_coordinate_size : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N n : ℕ) (L : Lat F) (α : GL (Fin 2) (ZMod N)) (ρ₀ : ℝ), L ≤ stdLat F → (∀ x ∈ stdLat F, (n : 𝓞 F) • x ∈ L) → (∀ v ∈ L, ∀ (j : Fin 2) (i : Emb F), Sz l lam ρ₀ ((i (v j) : ℝ) : ℂ)) → Sz l lam ρ₀ (N : ℂ) → ![0, (n : F)] ∈ twist N L (α : Matrix (Fin 2) (Fin 2) (ZMod N)) ∧ ∀ v ∈ twist N L (α : Matrix (Fin 2) (Fin 2) (ZMod N)), ∀ i : Emb F, Sz l lam ρ₀ ((i (v 0) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.HilbFam.TwistSize.main | exact GlobalTheory.HilbFam.TwistSize.main | (intros; apply GlobalTheory.HilbFam.TwistSize.main <;> assumption)
