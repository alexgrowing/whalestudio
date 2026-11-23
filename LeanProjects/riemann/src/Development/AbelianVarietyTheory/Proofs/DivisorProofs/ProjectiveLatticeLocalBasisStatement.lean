import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveLatticeLocalBasis
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiMapMemLocalSpan
open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent GlobalTheory.LatGlue
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (resG)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_lattice_local_basis : ∀ (R : Type) [CommRing R] [IsDomain R] (h : ℕ) (P : Submodule R (Fin h → R)), Module.Finite R P → Module.Projective R P → ∀ c : R, c ≠ 0 → (∀ x : Fin h → R, c • x ∈ P) → ∀ q : Ideal R, q.IsPrime → ∃ g ∉ q, ∃ b : Fin h → Fin h → R, (∀ l, b l ∈ P) ∧ (Matrix.of fun a l => b l a).det ≠ 0 ∧ ∀ u ∈ P, ∃ n : ℕ, g ^ n • u ∈ Submodule.span R (Set.range b) := by
  first | exact @GlobalTheory.LocFreeSub.exists_basis_near_prime | exact GlobalTheory.LocFreeSub.exists_basis_near_prime | (intros; apply GlobalTheory.LocFreeSub.exists_basis_near_prime <;> assumption)
