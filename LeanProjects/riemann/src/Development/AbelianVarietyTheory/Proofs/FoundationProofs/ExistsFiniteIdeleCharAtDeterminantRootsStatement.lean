import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFiniteIdeleCharAtDeterminantRoots
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteIdeleChar_at_determinantRoots : ∀ (D : D7) (V : HSp D) (c : (AE D)ˣ →* Circle), (∀ a, c (idF D a) = 1) → (∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → c x = 1) → ∃ xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ, ∀ (g : GA D V) (x : (AE D)ˣ), IsDetRoot V g x → ((xi (Matrix.GeneralLinearGroup.det (finHom V g)) : ℂˣ) : ℂ) = ((c x : Circle) : ℂ) := by
  first | exact @GlobalTheory.DetRootChar.exists_finite_char | exact GlobalTheory.DetRootChar.exists_finite_char | (intros; apply GlobalTheory.DetRootChar.exists_finite_char <;> assumption)
