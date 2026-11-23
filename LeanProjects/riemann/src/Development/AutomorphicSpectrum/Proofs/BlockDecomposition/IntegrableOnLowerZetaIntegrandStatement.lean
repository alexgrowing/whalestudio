import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOnLowerZetaIntegrand
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleCpowDetInverseTwist
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_lower_zeta_integrand : ∀ (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ) (c : HeckeCharacter ℚ),
  Ad3.R.G1a → Set0 μ 𝓕 mK 𝓓 → Aut H → IsOfFinOrder c → ∀ s : ℂ, 0 < s.re →
    IntegrableOn (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s) (𝓕 ∩ {g | Dt g < 1}) μ := by
  first | exact @GlobalTheory.CompanionTheory.RSZeta.integrableOn_low | exact GlobalTheory.CompanionTheory.RSZeta.integrableOn_low | (intros; apply GlobalTheory.CompanionTheory.RSZeta.integrableOn_low <;> assumption)
