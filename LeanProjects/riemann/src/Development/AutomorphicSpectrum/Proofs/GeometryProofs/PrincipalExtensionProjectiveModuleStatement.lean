import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalExtensionProjectiveModule
import Mathlib
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_extension_projective_module : ∀ (L : Type) [Field L] [NumberField L] (B : Type) [AddCommGroup B] [Module (𝓞 L) B] [Module.Finite (𝓞 L) B] [Module.Projective (𝓞 L) B] (I : Ideal (𝓞 L)), I ≠ ⊥ → ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L') (y : 𝓞 L'), I.map (algebraMap (𝓞 L) (𝓞 L')) = Ideal.span {y} ∧ ∀ (B' : Type) [AddCommGroup B'] [Module (𝓞 L') B'] [Module.Finite (𝓞 L') B'] [Module.Projective (𝓞 L') B'] (io : B →ₛₗ[algebraMap (𝓞 L) (𝓞 L')] B'), Submodule.span (𝓞 L') (Set.range io) = ⊤ → Module.finrank (𝓞 L') B' = Module.finrank (𝓞 L) B → ∃ e : Fin (Module.finrank (𝓞 L') B') → B', LinearIndependent (𝓞 L') e ∧ Submodule.span (𝓞 L') (Set.range e) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Basis.exists_basis_after_extension | exact GlobalTheory.CompanionTheory.Ar.Basis.exists_basis_after_extension | (intros; apply GlobalTheory.CompanionTheory.Ar.Basis.exists_basis_after_extension <;> assumption)
