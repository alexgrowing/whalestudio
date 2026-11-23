import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendIntegralPadicEvaluationGalois
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extend_integral_padic_evaluation_galois : ∀ (p : ℕ) [Fact p.Prime] (A B : Type) [CommRing A] [IsLocalRing A] [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B] [Finite (B ≃ₐ[A] B)] (𝔷 : Ideal B), Function.Injective (algebraMap A B) → (∀ b : B, (∀ σ : B ≃ₐ[A] B, σ b = b) → b ∈ Set.range (algebraMap A B)) → 𝔷.IsMaximal → ∀ ev : A →+* PadicAlgCl p, (∀ a, ‖ev a‖ ≤ 1) → (∀ a ∈ IsLocalRing.maximalIdeal A, ‖ev a‖ < 1) → ∃ ev' : B →+* PadicAlgCl p, (∀ a, ev' (algebraMap A B a) = ev a) ∧ (∀ b, ‖ev' b‖ ≤ 1) ∧ ∀ b ∈ 𝔷, ‖ev' b‖ < 1 := by
  first | exact @GlobalTheory.ValExt.exists_ext_centred | exact GlobalTheory.ValExt.exists_ext_centred | (intros; apply GlobalTheory.ValExt.exists_ext_centred <;> assumption)
