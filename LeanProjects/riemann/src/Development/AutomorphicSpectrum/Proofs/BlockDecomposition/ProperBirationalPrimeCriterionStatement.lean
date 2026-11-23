import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperBirationalPrimeCriterion
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_birational_prime_criterion : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}} (ψ : Z ⟶ J.subscheme) (V : X.Opens) (hV : IsAffineOpen V) (f : Γ(X, V)), IsIso (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f)) → ∀ (U : Z.Opens), IsAffineOpen U → ∀ h : U ≤ (ψ ≫ J.subschemeι) ⁻¹ᵁ V, letI : Algebra Γ(X, V) Γ(Z, U) := ((ψ ≫ J.subschemeι).appLE V U h).hom.toAlgebra; ∀ q : Ideal Γ(Z, U), q.IsPrime → f ∉ q.comap (algebraMap Γ(X, V) Γ(Z, U)) → (∀ c : Γ(Z, U), ∃ b t : Γ(X, V), t ∉ q.comap (algebraMap Γ(X, V) Γ(Z, U)) ∧ ∃ v : Γ(Z, U), v ∉ q ∧ v * (algebraMap Γ(X, V) Γ(Z, U) t * c) = v * algebraMap Γ(X, V) Γ(Z, U) b) ∧ (∀ b : Γ(X, V), (∃ v : Γ(Z, U), v ∉ q ∧ v * algebraMap Γ(X, V) Γ(Z, U) b = 0) → ∃ t : Γ(X, V), t ∉ q.comap (algebraMap Γ(X, V) Γ(Z, U)) ∧ t * b ∈ J.ideal ⟨V, hV⟩) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Krull.stalk_over_isoLocus | exact GlobalTheory.CompanionTheory.GE.Krull.stalk_over_isoLocus | (intros; apply GlobalTheory.CompanionTheory.GE.Krull.stalk_over_isoLocus <;> assumption)
