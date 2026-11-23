import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableBoundaryZetaTerm
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleCpowDetInverseTwist
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiable_boundary_zeta_term : ∀ (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ) (c : HeckeCharacter ℚ),
  Set0 μ 𝓕 mK 𝓓 → Aut H → Differentiable ℂ (GlobalTheory.CompanionTheory.RSZeta.Bd μ 𝓕 H c) := by
  first | exact @GlobalTheory.CompanionTheory.RSZeta.Bd_differentiable | exact GlobalTheory.CompanionTheory.RSZeta.Bd_differentiable | (intros; apply GlobalTheory.CompanionTheory.RSZeta.Bd_differentiable <;> assumption)
