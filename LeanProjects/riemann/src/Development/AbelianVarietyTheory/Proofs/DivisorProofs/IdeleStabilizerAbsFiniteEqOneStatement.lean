import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleStabilizerAbsFiniteEqOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DecayNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsInfEqOne

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idele_stabilizer_abs_finite_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    ∀ u ∈ GlobalTheory.IdeleTate.stab F E, GlobalTheory.IdeleTate.absFin F E u = 1 := by
  first | exact @GlobalTheory.IdeleTate.absFin_eq_one_of_mem_stab | exact GlobalTheory.IdeleTate.absFin_eq_one_of_mem_stab | (intros; apply GlobalTheory.IdeleTate.absFin_eq_one_of_mem_stab <;> assumption)
