import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesSchwartzReal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schroedinger_preserves_schwartz_real : ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] (β : LinearMap.BilinForm ℝ Y) (a b : Y)
    (f : SchwartzMap Y ℂ), ∃ g : SchwartzMap Y ℂ, ⇑g = sch β a b ⇑f := by
  first | exact @GlobalTheory.SchOp.sch_schwartz | exact GlobalTheory.SchOp.sch_schwartz | (intros; apply GlobalTheory.SchOp.sch_schwartz <;> assumption)
