import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnPeriodicFundamentalDomain
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFullL
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.OneVec
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_periodic_fundamental_domain : ∀ {g : ℕ} {V : Type} [NormedAddCommGroup V] (M : Submodule ℤ (Fl g)), IsLat M → ∀ (D : Set (Fl g)), IsAddFundamentalDomain M D volume → ∀ (φ : Fl g → V), Continuous φ → (∀ l ∈ M, ∀ x, φ (x + l) = φ x) → IntegrableOn φ D := by
  first | exact @GlobalTheory.integrableOn_periodic_of_isLat | exact GlobalTheory.integrableOn_periodic_of_isLat | (intros; apply GlobalTheory.integrableOn_periodic_of_isLat <;> assumption)
