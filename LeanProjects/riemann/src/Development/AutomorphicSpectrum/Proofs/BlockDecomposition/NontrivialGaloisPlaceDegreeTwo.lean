import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol

namespace GlobalTheory.CompanionTheory.QuadPlace

theorem finrank_eq_two_of_ne_refl : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (v : Pl) (w : PlK K) (_ : w.asIdeal.LiesOver v.asIdeal) (σ : Kv K w ≃ₐ[Qv v] Kv K w), σ ≠ AlgEquiv.refl → Module.finrank (Qv v) (Kv K w) = 2 := by
  classical
  intro K _ _ h2 v w hw σ hσ
  haveI := hw
  have hs := SemiLocal.sum_ramificationIdx_mul_inertiaDeg K v
  rw [h2] at hs
  have hle : Module.finrank (Qv v) (Kv K w) ≤ 2 := by
    rw [finrank_adicCompletion v w, ← hs]
    exact Finset.single_le_sum
      (f := fun b : SemiLocal.PlacesOver K v =>
        b.1.asIdeal.ramificationIdx (𝓞 ℚ) * b.1.asIdeal.inertiaDeg (𝓞 ℚ))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨w, hw⟩ : SemiLocal.PlacesOver K v))
  have hpos : 0 < Module.finrank (Qv v) (Kv K w) := Module.finrank_pos
  have hne : Module.finrank (Qv v) (Kv K w) ≠ 1 := by
    intro h1
    apply hσ
    have hbt := Subalgebra.bot_eq_top_of_finrank_eq_one (F := Qv v) (E := Kv K w) h1
    ext x
    have hx : x ∈ (⊥ : Subalgebra (Qv v) (Kv K w)) := by
      rw [hbt]
      exact Algebra.mem_top
    obtain ⟨y, rfl⟩ := Algebra.mem_bot.1 hx
    simp
  omega

end GlobalTheory.CompanionTheory.QuadPlace
