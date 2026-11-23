import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullbackOfKernelSup
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VanIdealHomog
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.is_pullback_of_kernel_sup : ∀ {X A B Z : Scheme.{0}} (a : A ⟶ X) (b : B ⟶ X) (f : Z ⟶ A) (g : Z ⟶ B)
    [IsClosedImmersion a] [IsClosedImmersion b] [IsClosedImmersion (f ≫ a)], f ≫ a = g ≫ b →
    Scheme.Hom.ker (f ≫ a) = Scheme.Hom.ker a ⊔ Scheme.Hom.ker b → IsPullback f g a b := by
  first | exact @GlobalTheory.CompanionTheory.GE.PbKer.isPullback_of_ker_eq_sup | exact GlobalTheory.CompanionTheory.GE.PbKer.isPullback_of_ker_eq_sup | (intros; apply GlobalTheory.CompanionTheory.GE.PbKer.isPullback_of_ker_eq_sup <;> assumption)
