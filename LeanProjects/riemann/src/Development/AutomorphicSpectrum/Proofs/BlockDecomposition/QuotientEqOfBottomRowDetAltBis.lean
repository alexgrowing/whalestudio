import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNxMul
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteAdelicGaussians.UpperRightUnipotentInvariance
import GroundTheory.AutomorphicForms.ReductionFinite
import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.GA
open scoped NumberField.AdeleRing Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_eq_of_lower_entries_eq_of_det_eq : ∀ (K : Type) [Field K] [NumberField K] (q q' : Ad3.K.GA.NQ K), (q.out : Matrix (Fin 2) (Fin 2) K) 1 0 = (q'.out : Matrix (Fin 2) (Fin 2) K) 1 0 → (q.out : Matrix (Fin 2) (Fin 2) K) 1 1 = (q'.out : Matrix (Fin 2) (Fin 2) K) 1 1 → (q.out : Matrix (Fin 2) (Fin 2) K).det = (q'.out : Matrix (Fin 2) (Fin 2) K).det → q = q' := by
  first | exact @GlobalTheory.CompanionTheory.GAKMajInj.maj_inj | exact GlobalTheory.CompanionTheory.GAKMajInj.maj_inj | (intros; apply GlobalTheory.CompanionTheory.GAKMajInj.maj_inj <;> assumption)
