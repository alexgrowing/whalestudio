import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrobeniusAutomorphismGcd
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPowRootOfUnity
open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.LKRes GlobalTheory.LKRes.ResSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobenius_automorphism_gcd : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → ∀ (f r : ℕ) (hq : qK p K = p ^ f), 0 < r → ∃ τ : Kn p K (r / Nat.gcd f r) ≃+* Kn p K (r / Nat.gcd f r), (∀ x, τ x = x ↔ (x : PadicAlgCl p) ∈ K) ∧ (∀ x, (⇑τ)^[r / Nat.gcd f r] x = x) ∧ ∀ b : Qr p r, τ (incQ p K hq r b) = incQ p K hq r ((frobQ p r ^ Nat.gcd f r) b) := by
  first | exact @GlobalTheory.LKRes.ResSplit.Tau.exists_tau | exact GlobalTheory.LKRes.ResSplit.Tau.exists_tau | (intros; apply GlobalTheory.LKRes.ResSplit.Tau.exists_tau <;> assumption)
