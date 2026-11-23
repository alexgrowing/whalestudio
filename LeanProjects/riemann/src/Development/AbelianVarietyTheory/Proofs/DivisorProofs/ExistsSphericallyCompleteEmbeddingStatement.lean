import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSphericallyCompleteEmbedding
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.Vert GlobalTheory.TriFrame GlobalTheory.FlagCell
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spherically_complete_embedding : ∀ (p : ℕ), p.Prime → ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K], (p : R) ∈ maximalIdeal R → Cardinal.mk R ≤ Cardinal.continuum → ∃ (C : SCF p) (θ : K →+* ↥C.S), (∀ a, ‖θ (algebraMap R K a)‖ ≤ 1) ∧ ∀ a ∈ maximalIdeal R, ‖θ (algebraMap R K a)‖ < 1 := by
  first | exact @GlobalTheory.TriFrame.exists_local_scf_embedding | exact GlobalTheory.TriFrame.exists_local_scf_embedding | (intros; apply GlobalTheory.TriFrame.exists_local_scf_embedding <;> assumption)
