import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesTestFunctionHolomorphicWeight
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinearStatement

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem thA_heis_entire_linear_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r g n : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → Even n → ∀ x ∈ X.dom, ∀ φ : TF n g, GlobalTheory.SW.IsSB φ → (∀ (y : Matrix (Fin n) (Fin r) E) (z : Fin n → Fin g → ℂ), GlobalTheory.SW.IsSB (heisG X bas y φ) ∧ thA X bas idx (heisG X bas y φ) x z = cexp (-(Real.pi * ∑ b, hx X bas idx x (z b + (1 / 2 : ℂ) • pv X idx x (y b)) (pv X idx x (y b)))) * thA X bas idx φ x (fun b => z b + pv X idx x (y b))) ∧ Differentiable ℂ (thA X bas idx φ x) ∧ (∀ φ' : TF n g, GlobalTheory.SW.IsSB φ' → (∀ a b : ℂ, GlobalTheory.SW.IsSB (a • φ + b • φ') ∧ thA X bas idx (a • φ + b • φ') x = a • thA X bas idx φ x + b • thA X bas idx φ' x) ∧ (thA X bas idx φ x = thA X bas idx φ' x → φ = φ')) := by
  intro E _ _ _ r g n X bas idx hs hn x hd φ hφ
  refine ⟨fun y z => ?_, GlobalTheory.SW.ThetaHol.differentiable_thA idx hs hφ hd, fun ψ hψ => ⟨fun a b => ?_, ?_⟩⟩
  · obtain ⟨h1, -, -, -, h2⟩ := (GlobalTheory.SW.heisG_laws E r X g bas idx n hs hn).2.2.2 y φ hφ
    exact ⟨h1, h2 x hd z⟩
  · have h1 : GlobalTheory.SW.IsSB (a • φ) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear _ _ _ _ _ hφ hφ).2.1 a
    have h2 : GlobalTheory.SW.IsSB (b • ψ) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear _ _ _ _ _ hψ hψ).2.1 b
    refine ⟨(GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear _ _ _ _ _ h1 h2).1, ?_⟩
    rw [GlobalTheory.SW.UnAct.thA_add idx hs hd h1 h2, GlobalTheory.SW.UnAct.thA_smul, GlobalTheory.SW.UnAct.thA_smul]
  · exact GlobalTheory.SW.UnAct.eq_of_thA_eq idx hs hd hφ hψ

end GlobalTheory.AdTh
