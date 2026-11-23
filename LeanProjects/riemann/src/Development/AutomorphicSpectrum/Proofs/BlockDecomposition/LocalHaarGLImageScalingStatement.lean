import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHaarGLImageScaling
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjOne
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_haar_GL_image_scaling : ∀ (D : D7) (n : ℕ) (a d : GL (Fin n) (AE D)) (b : hermA D n) (k₃ k₄ : Mx D n n) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F)) (lam : Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)), lam.IsAddHaarMeasure → (∀ (g : GL (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) (S : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)), lam ((fun x => g.1.mulVec x) '' S) = (absEv D.host.F D.host.E v (Matrix.GeneralLinearGroup.det g) : ℝ≥0∞) * lam S) → PositivityTheory.SiegelWeilFormula.Gen.IsCO (latAt a.1 v) → d.1 * k₃ = -1 → d.1 * k₄ = -(pull a b).1 → {x | ∃ y ∈ (latLoc D.host.F (stdLattice D.host.E n) v), ∃ y' ∈ (latLoc D.host.F (stdLattice D.host.E n) v), x = (PositivityTheory.SiegelWeilFormula.Gen.matV v k₃).mulVec y + (PositivityTheory.SiegelWeilFormula.Gen.matV v k₄).mulVec y'} = ((latLoc D.host.F (stdLattice D.host.E n) v) : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) → PositivityTheory.SiegelWeilFormula.Gen.nu2 lam (latAt a.1 v) (latAt (adj (a⁻¹).1) v) (PositivityTheory.SiegelWeilFormula.Gen.matV v b.1) = (absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v (Matrix.GeneralLinearGroup.det d)) : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.MM.NuFin.local_haar_GL_image_eq_absValue_det | exact GlobalTheory.CompanionTheory.MM.NuFin.local_haar_GL_image_eq_absValue_det | (intros; apply GlobalTheory.CompanionTheory.MM.NuFin.local_haar_GL_image_eq_absValue_det <;> assumption)
