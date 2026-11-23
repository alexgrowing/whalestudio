import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesPresentationUpToOrderTensorProductStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz.Chart

theorem eq_zero_of_ev_cube : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), (∀ n i, IsNilpotent ((Sum.elim (fun i => c.x n i ⊗ₜ[k] (1 : G.A n ⊗[k] G.A n)) (fun j => (1 : G.A n) ⊗ₜ[k] c.x₂ n j)) i)) ∧ ∀ f : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k, (∀ n (h : ∀ i, IsNilpotent ((Sum.elim (fun i => c.x n i ⊗ₜ[k] (1 : G.A n ⊗[k] G.A n)) (fun j => (1 : G.A n) ⊗ₜ[k] c.x₂ n j)) i)), evA k _ h f = 0) → f = 0 := by
  intro p k _ d G c
  have hnil : ∀ n i, IsNilpotent ((Sum.elim (fun i => c.x n i ⊗ₜ[k] (1 : G.A n ⊗[k] G.A n)) (fun j => (1 : G.A n) ⊗ₜ[k] c.x₂ n j)) i) := by
    intro n i
    cases i with
    | inl i => exact (c.nil n i).map (Algebra.TensorProduct.includeLeft (R := k) (S := k))
    | inr j => exact (c.nil₂ n j).map (Algebra.TensorProduct.includeRight (R := k))
  refine ⟨hnil, fun f hf => ?_⟩
  ext α
  obtain ⟨n, hn⟩ := c.presents.2 (α.degree + 1)
  have hs := c.presents.1 n
  have h2 := GlobalTheory.T.powerSeriesPresentation_up_to_order_tensorProduct k (Fin d) (Fin d) (G.A n) (G.A n) (c.x n) (c.nil n) (c.x n) (c.nil n)
    (c.nil₂ n) hs hs
  have h3 := GlobalTheory.T.powerSeriesPresentation_up_to_order_tensorProduct k (Fin d) (Fin d ⊕ Fin d) (G.A n) (G.A n ⊗[k] G.A n) (c.x n) (c.nil n)
    (c.x₂ n) (c.nil₂ n) (hnil n) hs h2.1
  have := (h3.2 (α.degree + 1) hn (h2.2 (α.degree + 1) hn hn) f (hf n (hnil n)) α (Nat.lt_succ_self _))
  simpa using this

end GlobalTheory.Katz.Chart
