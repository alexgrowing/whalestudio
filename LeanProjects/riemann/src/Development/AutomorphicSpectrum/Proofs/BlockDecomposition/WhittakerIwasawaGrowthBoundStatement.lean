import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerIwasawaGrowthBound
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.GTorus
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_iwasawa_growth_bound : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ψ : AddChar F Circle) (W' : GL (Fin 2) F → ℂ) (C : ℝ), (∀ x g, W' (Ad3.uni2 x * g) = (ψ x : ℂ) * W' g) → (∀ (a : Fˣ) g, W' (Ad3.dg2 a a * g) = W' g) → (∀ (a : Fˣ), ∀ κ ∈ GLnLocal.integralGL F 2, ‖W' (Ad3.dg2 a 1 * κ)‖ ≤ C * (modulus (a : F) : ℝ) ^ (1 / 4 : ℝ)) → ∀ (t₁ t₂ b₁ b₂ : Fˣ) (x : F), ∀ κ ∈ GLnLocal.integralGL F 2, ‖W' (Ad3.dg2 t₁ t₂ * (Ad3.uni2 x * Ad3.dg2 b₁ b₂ * κ))‖ ≤ C * (modulus ((t₁ * b₁ * (t₂ * b₂)⁻¹ : Fˣ) : F) : ℝ) ^ (1 / 4 : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.WhittakerIwasawa.whittaker_bound_iwasawa | exact GlobalTheory.CompanionTheory.WhittakerIwasawa.whittaker_bound_iwasawa | (intros; apply GlobalTheory.CompanionTheory.WhittakerIwasawa.whittaker_bound_iwasawa <;> assumption)
