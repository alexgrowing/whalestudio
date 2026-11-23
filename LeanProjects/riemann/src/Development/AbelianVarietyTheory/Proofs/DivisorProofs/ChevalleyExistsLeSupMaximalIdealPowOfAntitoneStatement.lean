import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChevalleyExistsLeSupMaximalIdealPowOfAntitone
import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chevalley_exists_le_sup_maximalIdeal_pow_of_antitone : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (K : ℕ → Ideal A) (J : Ideal A), Antitone K → (∀ e, maximalIdeal A ^ e ≤ K e) → (∀ (F : AdicCompletion (maximalIdeal A) A) (a : ℕ → A), (∀ n, F - algebraMap A (AdicCompletion (maximalIdeal A) A) (a n) ∈ maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n) → (∀ n, a n ∈ K n) → F ∈ J.map (algebraMap A (AdicCompletion (maximalIdeal A) A))) → ∀ k : ℕ, ∃ e : ℕ, K e ≤ J ⊔ maximalIdeal A ^ k := by
  first | exact @GlobalTheory.Chevalley.exists_le_sup_maximalIdeal_pow_of_antitone | exact GlobalTheory.Chevalley.exists_le_sup_maximalIdeal_pow_of_antitone | (intros; apply GlobalTheory.Chevalley.exists_le_sup_maximalIdeal_pow_of_antitone <;> assumption)
