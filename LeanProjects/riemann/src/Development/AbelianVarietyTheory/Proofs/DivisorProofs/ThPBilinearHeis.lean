import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThAHeisEntireLinearInjective
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardToMultisetEqDegree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PolyDerivMonomialOne

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem theta_bilinear_heisenberg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r g n : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → Even n → ∀ (q0 : ℕ) (hq : X.p0 + q0 = r), ∀ x ∈ X.dom, ∀ φ : TF n g, GlobalTheory.SW.IsSB φ → ∀ P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n), (∀ φ' : TF n g, GlobalTheory.SW.IsSB φ' → ∀ a b : ℂ, thP X hq bas idx (a • φ + b • φ') P x = a * thP X hq bas idx φ P x + b * thP X hq bas idx φ' P x) ∧ (∀ (P' : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) (a b : ℂ), thP X hq bas idx φ (a • P + b • P') x = a * thP X hq bas idx φ P x + b * thP X hq bas idx φ P' x) ∧ ∀ y : Matrix (Fin n) (Fin r) E, thP X hq bas idx (heisG X bas y φ) P x = ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P (letterDir X hq idx) (fun z => cexp (-(Real.pi * ∑ b, hx X bas idx x (z b + (1 / 2 : ℂ) • pv X idx x (y b)) (pv X idx x (y b)))) * thA X bas idx φ x (fun b => z b + pv X idx x (y b))) 0 := by
  intro E _ _ _ r g n X bas idx hs hn q0 hq x hd φ hφ P
  obtain ⟨h1, h2, h3⟩ := thA_heis_entire_linear_injective E r g n X bas idx hs hn x hd φ hφ
  refine ⟨fun ψ hψ a b => ?_, fun Q a b => ?_, fun y => ?_⟩
  · have h4 := (thA_heis_entire_linear_injective E r g n X bas idx hs hn x hd ψ hψ).2.1
    have e1 := GlobalTheory.Jet.polyDeriv_smul_fun P (letterDir X hq idx) h2 a 0
    have e2 := GlobalTheory.Jet.polyDeriv_smul_fun P (letterDir X hq idx) h4 b 0
    have e3 := GlobalTheory.Jet.polyDeriv_add_fun P (letterDir X hq idx) (h2.const_smul a) (h4.const_smul b) 0
    unfold thP
    rw [((h3 ψ hψ).1 a b).2, ← e1, ← e2]
    exact e3
  · unfold thP
    rw [ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_add, ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_smul, ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_smul]
  · unfold thP
    rw [funext fun z => (h1 y z).2]

end GlobalTheory.AdTh
