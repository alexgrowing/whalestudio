import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalZetaIntegralFunctionalEquation
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleCpowDetInverseTwist
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_zeta_integral_functional_equation : ∀ (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ) (Φ Φ' : (Fin 2 → 𝔸[ℚ]) → ℂ) (c : HeckeCharacter ℚ),
  Ad3.R.G1a → Ad3.R.G3 → Set0 μ 𝓕 mK 𝓓 → Aut H → Φ ∈ Adele2.schwartzBruhat2 ℚ → Φ' ∈ Adele2.schwartzBruhat2 ℚ →
  (∀ g, th Φ g + Φ 0 = (((Dt g)⁻¹ : ℝ) : ℂ) * (th Φ' (inv2 g) + Φ' 0)) →
  (∀ t : ℂ, 0 < t.re → IntegrableOn (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ t) (𝓕 ∩ {g | Dt g < 1}) μ) →
  ∀ s : ℂ, 1 < s.re → Zg μ 𝓕 H c Φ s = GlobalTheory.CompanionTheory.RSZeta.Zp μ 𝓕 H c Φ s + GlobalTheory.CompanionTheory.RSZeta.Zp μ 𝓕 H c⁻¹ Φ' (1 - s)
    + Φ' 0 * GlobalTheory.CompanionTheory.RSZeta.Jl μ 𝓕 H c (s - 1) - Φ 0 * GlobalTheory.CompanionTheory.RSZeta.Jl μ 𝓕 H c s := by
  first | exact @GlobalTheory.CompanionTheory.RSZeta.Zg_decomposition | exact GlobalTheory.CompanionTheory.RSZeta.Zg_decomposition | (intros; apply GlobalTheory.CompanionTheory.RSZeta.Zg_decomposition <;> assumption)
