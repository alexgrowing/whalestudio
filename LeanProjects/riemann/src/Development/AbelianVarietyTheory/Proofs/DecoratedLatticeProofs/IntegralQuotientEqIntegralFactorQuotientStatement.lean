import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralQuotientEqIntegralFactorQuotient
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_quotient_eq_integral_factor_quotient : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (G G₁ G₂ R K₁ K₂ : Subgroup H), IsClosed (G : Set H) → IsClosed (G₁ : Set H) → IsClosed (G₂ : Set H) → IsClosed (R : Set H) → G₁ ≤ G → G₂ ≤ G → (∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) → (∃ e : (G₁ × G₂) ≃ₜ G, ∀ p, (e p : H) = p.1 * p.2) → (∀ a ∈ G₁, ∀ b ∈ G₂, a * b ∈ R → a ∈ R ∧ b ∈ R) → K₁ ≤ G₁ → K₂ ≤ G₂ → IsCompact (K₁ : Set H) → IsCompact (K₂ : Set H) → IsOpen ((K₁.subgroupOf G₁ : Subgroup G₁) : Set G₁) → IsOpen ((K₂.subgroupOf G₂ : Subgroup G₂) : Set G₂) → ∀ (ρ : Measure (R.subgroupOf G)) (μ : Measure G) (ρ₁ : Measure (R.subgroupOf G₁)) (μ₁ : Measure G₁), ρ.IsHaarMeasure → μ.IsHaarMeasure → ρ₁.IsHaarMeasure → μ₁.IsHaarMeasure → ρ.IsInvInvariant → μ₁ {g | g.1 ∈ K₁} = 1 → ρ₁ {g | g.1.1 ∈ K₁} = 1 → ∀ (f : H → ℂ) (z : ℂ), (∀ r ∈ R, r ∈ G → ∀ g ∈ G, f (r * g) = f g) → (∀ k ∈ K₂, ∀ g ∈ G, f (g * k) = f g) → (∀ g ∈ G, f g ≠ 0 → ∃ r ∈ R, r ∈ G ∧ ∃ x ∈ G₁, ∃ k ∈ K₂, g = r * x * k) → IsQuotIntL1 ρ₁ μ₁ (fun x => f x.1) z → IsQuotIntL1 ρ μ (fun g => f g.1) (((μ.real {g | ∃ a ∈ K₁, ∃ b ∈ K₂, g.1 = a * b} / ρ.real {g | ∃ a ∈ K₁, ∃ b ∈ K₂, g.1.1 = a * b} : ℝ) : ℂ) * z) := by
  first | exact @GlobalTheory.CollapseFactor.collapse_factor | exact GlobalTheory.CollapseFactor.collapse_factor | (intros; apply GlobalTheory.CollapseFactor.collapse_factor <;> assumption)
