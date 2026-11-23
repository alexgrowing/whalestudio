import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameViaTwistedGenerators
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_via_twisted_generators : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (L : Lat ξ E) (r : ℕ) (V : Submodule Ω E) (m n : ℕ) (φ : Fin n → Module.Dual Ω E) (c : Fin r → E), CoordTie ℤ ξ x → L.IsVB r V → IsTwistGen ξ x L m φ → LinearIndependent Ω c → Submodule.span Ω (Set.range c) = V → ∃ B : Matrix (Fin r) (Fin n) Ω, B * Matrix.of (fun j l => φ j (c l)) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.exists_leftInverse_flagForms | exact GlobalTheory.CompanionTheory.Ar.FlagBun.exists_leftInverse_flagForms | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.exists_leftInverse_flagForms <;> assumption)
