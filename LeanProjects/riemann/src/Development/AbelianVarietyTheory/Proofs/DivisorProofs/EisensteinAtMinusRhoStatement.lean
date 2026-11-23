import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinAtMinusRho
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_at_minus_rho : GlobalTheory.ThK.KP → GlobalTheory.ConeSmall.EisAtMinusRho := by
  first | exact @GlobalTheory.ConeSmall.eisAtMinusRho | exact GlobalTheory.ConeSmall.eisAtMinusRho | (intros; apply GlobalTheory.ConeSmall.eisAtMinusRho <;> assumption)
