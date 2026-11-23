import Mathlib
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IntegralElementsGenericLinearSectionGaussPoint
import Formalism.LocalToGlobal.ProjectiveLattices.LocRingPf
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc
import ReciprocityTheory.SemistableReduction.AlgAll
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.RApprox
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_elements_generic_linear_section_gauss_point : ∀ (K Ω U : Type) [Field K] [Field Ω] [Field U] [Algebra K Ω] (f : Ω →+* U) (D N : ℕ), Algebra.trdeg K Ω = D → ∀ (v : Valuation U (WithZero (Multiplicative ℤ))) (t : Fin (D + 1) × Fin N → U) (x : Fin N → Ω), (∃ k, x k ≠ 0) → (∀ i : Fin D, ∑ k, t (i.succ, k) * f (x k) = 0) → (∀ p, v (t p) ≤ 1) → (∀ p : MvPolynomial (Fin (D + 1) × Fin N) K, (∀ α, v (f (algebraMap K Ω (p.coeff α))) ≤ 1) → (∃ α, v (f (algebraMap K Ω (p.coeff α))) = 1) → v (MvPolynomial.eval₂ (f.comp (algebraMap K Ω)) t p) = 1) → ∀ g ∈ Subfield.closure (Set.range f ∪ Set.range t), v g ≤ 1 → ∃ a ∈ Subring.closure ({u | u ∈ Set.range f ∧ v u ≤ 1} ∪ Set.range t), ∃ d ∈ Subring.closure ({u | u ∈ Set.range f ∧ v u ≤ 1} ∪ Set.range t), v d = 1 ∧ g * d = a := by
  first | exact @GlobalTheory.GaussSection.integral_elements | exact GlobalTheory.GaussSection.integral_elements | (intros; apply GlobalTheory.GaussSection.integral_elements <;> assumption)
