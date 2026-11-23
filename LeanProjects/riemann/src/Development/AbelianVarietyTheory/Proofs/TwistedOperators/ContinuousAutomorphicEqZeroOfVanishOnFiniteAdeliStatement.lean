import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousAutomorphicEqZeroOfVanishOnFiniteAdeli
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_automorphic_eq_zero_of_vanish_on_finiteAdelic : ∀ (D : D7) (V : HSp D) (φ : GA D V → ℂ), (∀ τ, (gramAt D V τ).PosDef) → Continuous φ → (∀ γ ∈ GQ V, ∀ h, φ (γ * h) = φ h) → (∀ h ∈ GfC V, φ h = 0) → ∀ h, φ h = 0 := by
  first | exact @GlobalTheory.Adopt.continuous_automorphic_eq_zero_of_vanish_on_finiteAdelic | exact GlobalTheory.Adopt.continuous_automorphic_eq_zero_of_vanish_on_finiteAdelic | (intros; apply GlobalTheory.Adopt.continuous_automorphic_eq_zero_of_vanish_on_finiteAdelic <;> assumption)
