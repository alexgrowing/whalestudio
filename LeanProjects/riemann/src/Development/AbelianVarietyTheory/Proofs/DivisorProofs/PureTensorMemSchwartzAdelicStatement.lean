import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorMemSchwartzAdelic
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPt

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pure_tensor_mem_schwartz_adelic : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ)
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = GlobalTheory.FinComm.indO v) →
    pure f φ ∈ schA F κ := by
  first | exact @GlobalTheory.PureIndO.pure_mem_schA | exact GlobalTheory.PureIndO.pure_mem_schA | (intros; apply GlobalTheory.PureIndO.pure_mem_schA <;> assumption)
