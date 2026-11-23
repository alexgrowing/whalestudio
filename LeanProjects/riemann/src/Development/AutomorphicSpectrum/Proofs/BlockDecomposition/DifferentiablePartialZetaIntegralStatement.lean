import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiablePartialZetaIntegral
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleCpowDetInverseTwist
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiable_partial_zeta_integral : ∀ (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ) (Φ : (Fin 2 → 𝔸[ℚ]) → ℂ) (c : HeckeCharacter ℚ),
  Ad3.R.G3 → Set0 μ 𝓕 mK 𝓓 → Aut H → Φ ∈ Adele2.schwartzBruhat2 ℚ → Differentiable ℂ (GlobalTheory.CompanionTheory.RSZeta.Zp μ 𝓕 H c Φ) := by
  first | exact @GlobalTheory.CompanionTheory.RSZeta.differentiable_Zp | exact GlobalTheory.CompanionTheory.RSZeta.differentiable_Zp | (intros; apply GlobalTheory.CompanionTheory.RSZeta.differentiable_Zp <;> assumption)
