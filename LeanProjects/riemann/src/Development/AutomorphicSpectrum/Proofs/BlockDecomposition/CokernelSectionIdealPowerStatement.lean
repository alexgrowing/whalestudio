import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CokernelSectionIdealPower
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cokernel_section_ideal_power : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [Z.Over (Spec (.of A))] (φ : Z ⟶ X) {E : X.Modules} (S : ℕ → Subobject E) (B : Subobject ((Scheme.Modules.pullback φ).obj E)) (n : ℕ), B ⊔ powSub I _ (n + 1) = pullSys I φ E S n → ∀ (V : X.Opens), ∀ x ∈ secs (S n) V, (show Γ(cokernel B.arrow, φ ⁻¹ᵁ V) from (adjMap φ B).app V x) ∈ Set.range ((idealPowι I (cokernel B.arrow) (n + 1)).app (φ ⁻¹ᵁ V)) := by
  first | exact @GlobalTheory.CompanionTheory.GE.PowImage.adjMap_app_mem_range_idealPowι | exact GlobalTheory.CompanionTheory.GE.PowImage.adjMap_app_mem_range_idealPowι | (intros; apply GlobalTheory.CompanionTheory.GE.PowImage.adjMap_app_mem_range_idealPowι <;> assumption)
