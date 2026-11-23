import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.GENSL
import GroundTheory.LocalFields.Different
import GroundTheory.LocalFields.LocalFourierTrace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LFunctionEquationGlobal

noncomputable section

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Global.AdicLiesOver Matrix
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.SplitLift

theorem split_place_degreeOne_embedding : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
    ∀ (v : Pl) (w₁ w₂ : PlK K) [w₁.asIdeal.LiesOver v.asIdeal] [w₂.asIdeal.LiesOver v.asIdeal],
      w₁ ≠ w₂ → Module.finrank (Qv v) (Kv K w₁) = 1 ∧
        ∀ ξ : K, algebraMap (Qv v) (Kv K w₁) (dg1 v w₁ ξ) = algebraMap K (Kv K w₁) ξ := by
  intro K _ _ h2 v w₁ w₂ _ _ hne
  have h1 : Module.finrank (Qv v) (Kv K w₁) = 1 := (GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.places_split h2 v w₁ w₂ hne).2.1
  refine ⟨h1, fun ξ => ?_⟩
  have hs : ∀ y : Kv K w₁, ∃ a : Qv v, algebraMap (Qv v) (Kv K w₁) a = y := fun y => by
    have hb := Subalgebra.bot_eq_top_of_finrank_eq_one h1
    have hy : y ∈ (⊥ : Subalgebra (Qv v) (Kv K w₁)) := by rw [hb]; trivial
    exact Algebra.mem_bot.1 hy
  exact Function.invFun_eq (hs _)

end GlobalTheory.CompanionTheory.SplitLift
