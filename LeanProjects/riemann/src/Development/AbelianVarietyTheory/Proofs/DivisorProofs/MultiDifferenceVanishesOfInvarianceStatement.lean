import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiDifferenceVanishesOfInvariance
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multi_difference_vanishes_of_invariance : ∀ (A : Type 1) [AddCommGroup A] (f : A → ℤ) (d : ℕ), DiffVanish (d + 1) f → ∀ (N : ℕ) (g : Fin N → A) (p : ℕ), 2 ≤ p → (∀ (a : ℕ) (c : A), ∑ i, f (p ^ a • g i + c) = (N : ℤ) * f c) → ∀ (m D : ℕ) (S : Finset (Fin D)), S.Nonempty → ∀ P : Fin D → A, ∑ i, multiDiff (fun j => if j ∈ S then m • g i else P j) f 0 = 0 := by
  first | exact @GlobalTheory.FinDiffPow.sum_multiDiff_eq_zero | exact GlobalTheory.FinDiffPow.sum_multiDiff_eq_zero | (intros; apply GlobalTheory.FinDiffPow.sum_multiDiff_eq_zero <;> assumption)
