import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanDecayOperatorApplyMemAdelicSchwartz
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanDecayOperatorApply_mem_adelicSchwartz : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (o : Op F κ), ∀ f ∈ schA F κ, app F o f ∈ schA F κ := by
  first | exact @GlobalTheory.ArchDecay.SchAStab.app_mem_schA | exact GlobalTheory.ArchDecay.SchAStab.app_mem_schA | (intros; apply GlobalTheory.ArchDecay.SchAStab.app_mem_schA <;> assumption)
