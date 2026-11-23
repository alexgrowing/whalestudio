import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftBaseChangeDualBijective

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.ChainDesc

theorem finite_projective_sections_of_isVB :
    ∀ (X : Scheme.{0}) (F : X.Modules) (r : ℕ), GlobalTheory.VB.IsVB F r → ∀ U : X.Opens, IsAffineOpen U →
      Module.Finite Γ(X, U) Γ(F, U) ∧ Module.Projective Γ(X, U) Γ(F, U) := by
  intro X F r h U hU
  obtain ⟨h₁, h₂⟩ := GlobalTheory.ChainPts.SecPair.finitePresentation_projective h hU
  exact ⟨inferInstance, h₂⟩

end GlobalTheory.ChainDesc
