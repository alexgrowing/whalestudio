import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedExtensionProductDecomposition
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_extension_product_decomposition : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → ∀ (f r : ℕ), qK p K = p ^ f → 0 < r → ∃ (e : KQ p K r ≃+* (Fin (Nat.gcd f r) → Kn p K (r / Nat.gcd f r))) (τ : Kn p K (r / Nat.gcd f r) ≃+* Kn p K (r / Nat.gcd f r)), (∀ x, (τ x = x ↔ (x : PadicAlgCl p) ∈ K)) ∧ (∀ x, (⇑τ)^[r / Nat.gcd f r] x = x) ∧ (∀ (a : K) (i : Fin (Nat.gcd f r)), ((e (inclK p K r a) i : Kn p K (r / Nat.gcd f r)) : PadicAlgCl p) = a) ∧ (∀ (x : KQ p K r) (i : Fin (Nat.gcd f r)) (h : i.val + 1 < Nat.gcd f r), e (sigKQ p K r x) i = e x ⟨i.val + 1, h⟩) ∧ (∀ (x : KQ p K r) (i : Fin (Nat.gcd f r)), i.val + 1 = Nat.gcd f r → ∀ (i0 : Fin (Nat.gcd f r)), i0.val = 0 → e (sigKQ p K r x) i = τ (e x i0)) ∧ (∀ x : KQ p K r, x ∈ intKQ p K r ↔ ∀ i, e x i ∈ GlobalTheory.LKLoc.intR p K (r / Nat.gcd f r)) := by
  first | exact @GlobalTheory.LKRes.ResSplit.kq_split | exact GlobalTheory.LKRes.ResSplit.kq_split | (intros; apply GlobalTheory.LKRes.ResSplit.kq_split <;> assumption)
