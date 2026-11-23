import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineRestrictionFunctionsNaturality
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeIffAffineSections
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalFunctions
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RelSerreSections
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_restriction_functions_naturality : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] (φ : Z ⟶ X) (V : X.Opens) (hV : IsAffineOpen V) [IsNoetherianRing Γ(X, V)], letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩; (∀ (W : (φ ⁻¹ᵁ V).toScheme.Opens) (a : A), ((φ ⁻¹ᵁ V).ι.appIso W).hom (toFunctions (A := A) ((φ ⁻¹ᵁ V).ι ''ᵁ W) a) = toFunctions (A := Γ(X, V)) W (toFunctions (A := A) V a)) → ∀ (G : Z.Modules) [G.IsQuasicoherent] (m : ℕ), ∃ g : (idealPow I G m).restrict (φ ⁻¹ᵁ V).ι ⟶ idealPow (Ideal.map (toFunctions (A := A) V) I) (G.restrict (φ ⁻¹ᵁ V).ι) m, g ≫ idealPowι (Ideal.map (toFunctions (A := A) V) I) (G.restrict (φ ⁻¹ᵁ V).ι) m = (Scheme.Modules.restrictFunctor (φ ⁻¹ᵁ V).ι).map (idealPowι I G m) := by
  first | exact @GlobalTheory.CompanionTheory.GE.FormalShift.restrict_idealPow_lift | exact GlobalTheory.CompanionTheory.GE.FormalShift.restrict_idealPow_lift | (intros; apply GlobalTheory.CompanionTheory.GE.FormalShift.restrict_idealPow_lift <;> assumption)
