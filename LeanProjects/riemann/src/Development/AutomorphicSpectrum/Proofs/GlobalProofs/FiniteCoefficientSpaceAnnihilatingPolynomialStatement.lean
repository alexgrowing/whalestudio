import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteCoefficientSpaceAnnihilatingPolynomial
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IoInjective
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SkewOfCommute
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_coefficient_space_annihilating_polynomial : ∀ (K W : Type) [Group K] [TopologicalSpace K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ K W), GlobalTheory.Published.AutFin.IsContRep ρ → ∀ s : ℝ → K, Continuous s → s 0 = 1 → (∀ a b, s (a + b) = s a * s b) → ∃ m : Polynomial ℂ, m ≠ 0 ∧ ∀ f ∈ GlobalTheory.Published.AutFin.coeffSpan ρ, ∀ k : K, ∑ j ∈ Finset.range (m.natDegree + 1), m.coeff j * iteratedDeriv j (fun t : ℝ => f (k * s t)) 0 = 0 := by
  first | exact @GlobalTheory.CompanionTheory.HcFinite.OneParam.coeff_ode | exact GlobalTheory.CompanionTheory.HcFinite.OneParam.coeff_ode | (intros; apply GlobalTheory.CompanionTheory.HcFinite.OneParam.coeff_ode <;> assumption)
