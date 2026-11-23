import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamagawaMeasureMatrixAdeles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tamagawa_measure_matrix_adeles : ∀ (D : D7) (m n d : ℕ) (ε : Module.Basis (Fin d) D.host.F D.host.E) (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)), IsCovolOne (ratMx D m n) μ 𝓕 → ∀ [MeasurableSpace (Fin m × Fin n × Fin d → AF D.host.F)] [BorelSpace (Fin m × Fin n × Fin d → AF D.host.F)], ∃ μ' : Measure (Fin m × Fin n × Fin d → AF D.host.F), IsTamagawa D.host.F (Fin m × Fin n × Fin d) μ' ∧ ∀ f : (Fin m × Fin n × Fin d → AF D.host.F) → ℂ, ∫ y, f y ∂μ' = ∫ x, f (coord ε x) ∂μ := by
  first | exact @GlobalTheory.SWLinkMeas.exists_isTamagawa | exact GlobalTheory.SWLinkMeas.exists_isTamagawa | (intros; apply GlobalTheory.SWLinkMeas.exists_isTamagawa <;> assumption)
