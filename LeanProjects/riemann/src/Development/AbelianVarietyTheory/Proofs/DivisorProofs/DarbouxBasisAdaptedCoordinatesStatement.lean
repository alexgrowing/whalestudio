import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxBasisAdaptedCoordinates
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
theorem _root_.GlobalTheory.T.darboux_basis_adapted_coordinates : ∀ (D : D7) (n : ℕ) (V : HSp D) (J : Matrix (Fin n) (Fin n) D.host.E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (T : GL (Fin (n + n)) D.host.E), IsWittBasis D.sp.cm.sig J 1 T → T.1ᵀ * J₂ * T.1.map D.sp.cm.sig = GlobalTheory.StdUnn.Jst D n → ∀ (d : ℕ) (ε : Module.Basis (Fin d) D.host.F D.host.E), ∃ co : Dbx V J₂ d, IsAdapted D.sp.cm.sig co ∧ IsCoord V T ε co := by
  first | exact @GlobalTheory.SWLink.Darb.exists_adapted | exact GlobalTheory.SWLink.Darb.exists_adapted | (intros; apply GlobalTheory.SWLink.Darb.exists_adapted <;> assumption)
