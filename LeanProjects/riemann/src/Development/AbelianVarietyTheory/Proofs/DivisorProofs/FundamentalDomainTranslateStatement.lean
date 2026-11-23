import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainTranslate
import Mathlib

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_translate : ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] (Q : Subgroup G) (𝓓 : Set G) (m : G), IsFundamentalDomain Q 𝓓 μ → IsFundamentalDomain (Q.map (MulAut.conj m⁻¹).toMonoidHom) ((fun g => m⁻¹ * g) '' 𝓓) μ ∧ ∀ φ : G → ENNReal, ∫⁻ g in 𝓓, φ (m⁻¹ * g) ∂μ = ∫⁻ g in (fun g => m⁻¹ * g) '' 𝓓, φ g ∂μ := by
  first | exact @GlobalTheory.fundamentalDomain_translate_conj | exact GlobalTheory.fundamentalDomain_translate_conj | (intros; apply GlobalTheory.fundamentalDomain_translate_conj <;> assumption)
