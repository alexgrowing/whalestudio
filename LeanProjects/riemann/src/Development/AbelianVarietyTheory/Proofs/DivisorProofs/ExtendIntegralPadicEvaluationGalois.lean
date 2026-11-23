import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeOneOfExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.ValExt

noncomputable def unitBall (p : ℕ) [Fact p.Prime] : ValuationSubring (PadicAlgCl p) :=
  (Valued.v : Valuation (PadicAlgCl p) NNReal).valuationSubring

theorem exists_ext_centred : ∀ (p : ℕ) [Fact p.Prime] (A B : Type) [CommRing A] [IsLocalRing A] [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B] [Finite (B ≃ₐ[A] B)] (𝔷 : Ideal B), Function.Injective (algebraMap A B) → (∀ b : B, (∀ σ : B ≃ₐ[A] B, σ b = b) → b ∈ Set.range (algebraMap A B)) → 𝔷.IsMaximal → ∀ ev : A →+* PadicAlgCl p, (∀ a, ‖ev a‖ ≤ 1) → (∀ a ∈ IsLocalRing.maximalIdeal A, ‖ev a‖ < 1) → ∃ ev' : B →+* PadicAlgCl p, (∀ a, ev' (algebraMap A B a) = ev a) ∧ (∀ b, ‖ev' b‖ ≤ 1) ∧ ∀ b ∈ 𝔷, ‖ev' b‖ < 1 := by
  first
  | exact @_root_.GlobalTheory.NormExtensionBound.main
  | exact _root_.GlobalTheory.NormExtensionBound.main
  | (apply _root_.GlobalTheory.NormExtensionBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormExtensionBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormExtensionBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormExtensionBound.main ..)

end GlobalTheory.ValExt
