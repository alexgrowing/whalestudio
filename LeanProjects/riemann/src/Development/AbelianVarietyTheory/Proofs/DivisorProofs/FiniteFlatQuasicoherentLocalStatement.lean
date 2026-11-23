import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatQuasicoherentLocal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_flat_quasicoherent_local : ∀ (O : Type) [CommRing O] {X Y : Scheme.{0}} [Algebra O Γ(X, ⊤)] [Algebra O Γ(Y, ⊤)] (f : Y ⟶ X), (∀ r : O, f.appTop (algebraMap O Γ(X, ⊤) r) = algebraMap O Γ(Y, ⊤) r) → ∀ (V : X.Opens) (n : ℕ), IsAffineOpen V → IsAffineOpen (f ⁻¹ᵁ V) → (letI := (f.app V).hom.toAlgebra; Module.Free Γ(X, V) Γ(Y, f ⁻¹ᵁ V) ∧ Module.Finite Γ(X, V) Γ(Y, f ⁻¹ᵁ V) ∧ Module.finrank Γ(X, V) Γ(Y, f ⁻¹ᵁ V) = n) → ∀ (G : X.Modules) [G.IsQuasicoherent], Module.length O (sectionsOn ((Scheme.Modules.pullback f).obj G) (f ⁻¹ᵁ V)) = n * Module.length O (sectionsOn G V) := by
  first | exact @GlobalTheory.length_sectionsOn_pullback_of_free | exact GlobalTheory.length_sectionsOn_pullback_of_free | (intros; apply GlobalTheory.length_sectionsOn_pullback_of_free <;> assumption)
