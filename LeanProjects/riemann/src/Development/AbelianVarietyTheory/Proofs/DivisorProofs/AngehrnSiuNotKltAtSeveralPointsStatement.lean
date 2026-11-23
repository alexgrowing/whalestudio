import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AngehrnSiuNotKltAtSeveralPoints
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.angehrnSiu_not_klt_at_several_points : GlobalTheory.Published.Principalisation →
  ∀ {K κ : Type} [Field K] [Field κ] [Algebra ℂ K] [Algebra ℂ κ] (n k c l M : ℕ) (R : Fin c → Subring K)
    (π : ∀ i, R i →+* κ) (w : ∀ i, Fin l → R i) (lam : Fin c → κ) (wb : Fin l → κ),
  (∃ x : Fin n → K, TrBasis (algebraMap ℂ K) x) → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) → 1 ≤ k →
  (∀ i, IsLocModel (algebraMap ℂ K) (R i) ∧ IsIntegrallyClosed (R i) ∧ RatRes (algebraMap ℂ K) (R i)) →
  (∀ i a (h : algebraMap ℂ K a ∈ R i), π i ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ i (f : κ), ∃ a b : R i, π i b ≠ 0 ∧ f * π i b = π i a) →
  (∀ i, IsLocModel (algebraMap ℂ κ) (π i).range ∧ RatRes (algebraMap ℂ κ) (π i).range) →
  (∀ i, lam i ≠ 0 ∧ ∀ j, π i (w i j) = lam i * wb j) →
  c * (M + k - 1).choose k < l → 1 ≤ M →
  ∃ a : Fin l → ℂ, a ≠ 0 ∧ ∀ (i : Fin c) (xi : Fin n → R i) (φ : R i →₀ ℚ) (u s : R i) (t : ℚ),
    TrBasis (algebraMap ℂ K) (fun j => (xi j : K)) → (∀ g ∈ φ.support, g ≠ 0) →
    EffAt (algebraMap ℂ K) n (R i) (dForm (algebraMap ℂ K) (fun j => (xi j : K)))
      (Finsupp.mapDomain (fun g : R i => (g : K)) φ) →
    π i u = 0 → 0 ≤ t → (s : K) = ∑ j, algebraMap ℂ K (a j) * (w i j : K) + u → (s : K) ≠ 0 →
    ((Function.Injective (π i) ∧ (k : ℚ) ≤ t * M) ∨
      ∃ E : Place (algebraMap ℂ K), E.Contains (R i) ∧ (∀ r : R i, (r : K) ≠ 0 → (π i r = 0 ↔ 0 < E.ord r)) ∧
        (k : ℚ) + M * (E.disc (dForm (algebraMap ℂ K) (fun j => (xi j : K)))
          (Finsupp.mapDomain (fun g : R i => (g : K)) φ) + 1) ≤ t * M) →
    ¬ Klt (algebraMap ℂ K) n (R i) (dForm (algebraMap ℂ K) (fun j => (xi j : K)))
      (Finsupp.mapDomain (fun g : R i => (g : K)) φ + Finsupp.single (s : K) t) := by
  first | exact @GlobalTheory.LocalHeart.not_klt_at_points | exact GlobalTheory.LocalHeart.not_klt_at_points | (intros; apply GlobalTheory.LocalHeart.not_klt_at_points <;> assumption)
