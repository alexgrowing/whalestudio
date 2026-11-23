import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionExtendsFromStalkPullback
import Mathlib
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_extends_from_stalk_pullback : ∀ {X Y Z : Scheme.{0}} (π : Y ⟶ X) (p : X) (y₀ : Y), π y₀ = p → ∀ (c : Z ⟶ pullback π (X.fromSpecStalk p)) [IsClosedImmersion c] (s : Γ(Z, ⊤)), ∃ (W : Y.Opens) (f : Γ(Y, W)), y₀ ∈ W ∧ ((c ≫ pullback.fst π (X.fromSpecStalk p)).app W).hom f = Z.presheaf.map (homOfLE (le_top : (c ≫ pullback.fst π (X.fromSpecStalk p)) ⁻¹ᵁ W ≤ ⊤)).op s := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.LocalLift.exists_open_extension | exact GlobalTheory.CompanionTheory.Ggeo.LocalLift.exists_open_extension | (intros; apply GlobalTheory.CompanionTheory.Ggeo.LocalLift.exists_open_extension <;> assumption)
