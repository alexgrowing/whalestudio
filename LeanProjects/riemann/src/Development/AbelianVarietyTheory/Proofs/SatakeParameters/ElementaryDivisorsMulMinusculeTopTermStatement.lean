import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementaryDivisorsMulMinusculeTopTerm
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elementaryDivisors_mul_minuscule_top_term : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (n : ℕ), Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → ∀ (d : Fin n → ℕ) (k : ℕ), Antitone d → (∀ i : Fin n, 0 < d i ↔ (i : ℕ) < k) → ∀ (g a : GL (Fin n) L), (∃ k₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L), ∃ k₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L), ((k₁ * g * k₂ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal fun i => ϖ ^ (d i - 1)) → (∃ k₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L), ∃ k₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L), ((k₁ * a * k₂ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal fun i : Fin n => if (i : ℕ) < k then ϖ else 1) → ∀ d' : Fin n → ℕ, Antitone d' → (∃ k₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L), ∃ k₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L), ((k₁ * (g * a) * k₂ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal fun i => ϖ ^ d' i) → d' = d ∨ (∑ i, d' i = ∑ i, d i ∧ ∑ i, d' i ^ 2 < ∑ i, d i ^ 2) := by
  first | exact @GlobalTheory.Hk3.MinuscTop.elemDiv_mul_minuscule | exact GlobalTheory.Hk3.MinuscTop.elemDiv_mul_minuscule | (intros; apply GlobalTheory.Hk3.MinuscTop.elemDiv_mul_minuscule <;> assumption)
